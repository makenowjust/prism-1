# frozen_string_literal: true

module Prism
  # The pattern virtual machine is responsible for compiling a pattern into a
  # set of instructions that can be used to match against nodes. The virtual
  # machine instructions are:
  #
  # checklength <length>, <label>
  #
  # - Check that the length of the value on the top of the stack is equal to the
  #   given length. If it is not, then jump to the given label. Otherwise fall
  #   through to the next instruction.
  #
  # checknil <label>
  #
  # - Check that the value on the top of the stack is nil. If it is not, then
  #   jump to the given label. Otherwise fall through to the next instruction.
  #
  # checkobject <object>, <label>
  #
  # - Check that the value on the top of the stack is equal to the given object
  #   using the === method. If it is not, then jump to the given label.
  #   Otherwise fall through to the next instruction.
  #
  # checktype <type>, <label>
  #
  # - Check that the value on the top of the stack is an instance of the given
  #   type. If it is not, then jump to the given label. Otherwise fall through
  #   to the next instruction.
  #
  # fail
  #
  # - Immediately fail the pattern matching.
  #
  # jump <label>
  #
  # - Jump directly to the given label.
  #
  # opt_splittype <split>, <label>
  #
  # - Check the type of the value on the top of the stack using the #type
  #   method. The split object is a hash that maps types to labels. If the type
  #   is in the split object, then jump to the label. Otherwise jump directly to
  #   the given label.
  #
  # pushfield <name>
  #
  # - Fetch the field from the object on the top of the stack using the named
  #   method. Push the value onto the stack.
  #
  # pushindex <index>
  #
  # - Fetch the index from the object on the top of the stack using the given
  #   index and the [] method. Push the value onto the stack.
  #
  # pop
  #
  # - Pop the top value off of the stack.
  #
  class PatternVM
    # Raised when the query given to a pattern is either invalid Ruby syntax or
    # is using syntax that we don't yet support.
    class CompilationError < StandardError
      def initialize(repr)
        super(<<~ERROR)
          prism was unable to compile the pattern you provided into a usable
          expression. It failed on to understand the node represented by:

          #{repr}

          Note that not all syntax supported by Ruby's pattern matching syntax
          is also supported by prism's patterns. If you're using some syntax
          that you believe should be supported, please open an issue on
          GitHub at https://github.com/ruby/prism/issues/new.
        ERROR
      end
    end

    # Raised when a field is attempting to be matched by a pattern that will
    # never be possible based prism's configuration.
    class IncompatibleFieldError < StandardError
      def initialize(field, type)
        super(<<~ERROR)
          prism was unable to compile the pattern you provided into a usable
          expression because the #{field} field can never be matched by #{type}.
        ERROR
      end
    end

    # Raised when a constant path is used that is not understood.
    class NameError < StandardError
      def initialize(name)
        super(<<~ERROR)
          prism was unable to find the constant that you provided. It failed on
          the constant path:

          #{name}

          Note that not all constant paths are supported by prism's patterns.
          If you're using some constant path that you believe should be
          supported, please open an issue on GitHub at
          https://github.com/ruby/prism/issues/new.
        ERROR
      end
    end

    # A label is a placeholder for a jump instruction. While building our set of
    # instructions, they are placed into the list of instructions until we know
    # where they should actually be jumping to. Once we do, we can replace the
    # label with the correct PC.
    class Label
      attr_accessor :pc
      attr_reader :jumps, :splits

      def initialize(pc = -1)
        @pc = pc
        @jumps = []
        @splits = []
      end

      def push_jump(pc)
        jumps << pc
      end

      def push_split(pc, type)
        splits << [pc, type]
      end
    end

    # The pattern that this VM is compiling. This is represented as a string
    # with a valid Ruby pattern matching expressions.
    attr_reader :pattern

    # The list of instructions that this VM has compiled. This is an array of
    # symbols and objects that represent the flow of the bytecode.
    attr_reader :insns

    # The list of labels that this VM has compiled. This is an array of labels
    # that are used to represent jumps in the bytecode.
    attr_reader :labels

    attr_reader :checking_type, :passing, :failing

    def initialize(pattern)
      @pattern = pattern

      @insns = []
      @labels = []

      @checking_type = true
      @passing = nil
      @failing = nil
    end

    ############################################################################
    # These methods are the public API of the pattern class.                   #
    ############################################################################

    # Combine two patterns together into a new pattern that will match either
    # of the two patterns.
    def or(other)
      PatternVM.new("#{pattern} | #{other.pattern}")
    end
    alias | or

    # Compile the pattern into a set of instructions that can be used to match
    # against nodes.
    def compile
      visit(Prism.parse("nil in #{pattern}").value.statements.body.first)
    end

    # Disassemble the instructions that this VM has compiled into a
    # human-readable format.
    def disasm
      output = +""
      each_insn do |pc, insn|
        case insn
        when :checklength
          output << "%04d %-16s %d, %s\n" % [pc, insn, insns[pc + 1], disasm_label(insns[pc + 2])]
        when :checknil
          output << "%04d %-16s %s\n" % [pc, insn, disasm_label(insns[pc + 1])]
        when :checkobject
          output << "%04d %-16s %s, %s\n" % [pc, insn, insns[pc + 1].inspect, disasm_label(insns[pc + 2])]
        when :checktype
          output << "%04d %-16s %s, %s\n" % [pc, insn, insns[pc + 1], disasm_label(insns[pc + 2])]
        when :fail
          output << "%04d %-16s\n" % [pc, insn]
        when :jump
          output << "%04d %-16s %s\n" % [pc, insn, disasm_label(insns[pc + 1])]
        when :opt_splittype
          output << "%04d %-16s %s, %s\n" % [pc, insn, disasm_split(insns[pc + 1]), disasm_label(insns[pc + 2])]
        when :pushfield
          output << "%04d %-16s %s\n" % [pc, insn, insns[pc + 1]]
        when :pushindex
          output << "%04d %-16s %d\n" % [pc, insn, insns[pc + 1]]
        when :pop
          output << "%04d %-16s\n" % [pc, insn]
        else
          output << "%04d:\n" % pc
        end
      end

      output
    end

    # Run the instructions that this VM has compiled against a node. This will
    # return true if the node matches the pattern and false if it does not.
    def call(node)
      stack = [node]

      pc = 0
      max_pc = insns.length

      while pc < max_pc
        case insns[pc]
        when :checklength
          if stack[-1].length == insns[pc + 1]
            pc += 3
          else
            pc = insns[pc + 2]
          end
        when :checknil
          if stack[-1].nil?
            pc += 2
          else
            pc = insns[pc + 1]
          end
        when :checkobject
          if insns[pc + 1] === stack[-1]
            pc += 3
          else
            pc = insns[pc + 2]
          end
        when :checktype
          if stack[-1].is_a?(insns[pc + 1])
            pc += 3
          else
            pc = insns[pc + 2]
          end
        when :fail
          return false
        when :jump
          pc = insns[pc + 1]
        when :opt_splittype
          pc = insns[pc + 1].fetch(stack[-1].type, insns[pc + 2])
        when :pushfield
          stack.push(stack[-1].public_send(insns[pc + 1]))
          pc += 2
        when :pushindex
          stack.push(stack[-1][insns[pc + 1]])
          pc += 2
        when :pop
          stack.pop
          pc += 1
        else
          raise "Unknown instruction: #{insns[pc].inspect}"
        end
      end

      true
    end

    ############################################################################
    # These methods are used to compile nodes.                                 #
    ############################################################################

    # in foo | bar
    def visit_alternation_pattern_node(node)
      # First, find all of the clauses that are held by alternation pattern
      # nodes. This will let us do further optimizations if we can split on a
      # common check.
      clauses = [node.left, node.right]
      while clauses.first.is_a?(AlternationPatternNode)
        clause = clauses.shift
        clauses.unshift(clause.left, clause.right)
      end

      # Next, we're going to check on the kinds of patterns that we're trying
      # to compile. If it's possible to take advantage of checking the type
      # only once, then we will do that.
      types =
        clauses.group_by do |clause|
          constant_node =
            case clause.type
            when :array_pattern_node, :find_pattern_node, :hash_pattern_node
              clause.constant
            when :constant_read_node, :constant_path_node
              clause
            end

          if constant_node
            constant = constant_for(constant_node)
            (constant < Node) ? constant.type : :ungrouped
          else
            :ungrouped
          end
        end

      # If we have more than one type, we can do a special optimization where
      # we check the type once and then jump to the correct clause.
      if !types.key?(:ungrouped) && types.length > 1
        labels = types.transform_values { label }
        opt_splittype(labels, failing)

        types.each do |type, clauses|
          pushlabel(labels[type])

          parent_failing = failing
          parent_checking_type = checking_type
          @checking_type = false

          last_index = clauses.length - 1
          clauses.each_with_index do |clause, index|
            @failing = label if index != last_index

            # We don't need to check the type since we're explicitly splitting
            # on type already. In this case for constant nodes we can skip
            # visiting those nodes entirely. For other nodes, we'll rely on the
            # @checking_type flag to skip the check.
            case clause.type
            when :constant_path_node, :constant_read_node
            else
              visit(clause)
            end

            jump(passing)
            pushlabel(@failing) if index != last_index
          end

          @failing = parent_failing
          @checking_type = parent_checking_type
        end
      else
        # If there is an ungrouped type or there is only a single type, there's
        # no benefit to calling the #type method, so we'll compile as normal.
        # We do this by first checking the left, then checking the right.
        parent_failing = failing
        @failing = label

        visit(node.left)
        jump(passing)

        pushlabel(@failing)
        @failing = parent_failing
        visit(node.right)

        jump(passing)
      end
    end

    # in [foo, bar, baz]
    def visit_array_pattern_node(node)
      if !node.rest.nil? || node.posts.any?
        raise CompilationError, node.inspect
      end

      if checking_type
        if node.constant
          visit(node.constant)
        else
          checktype(Array, failing)
        end
      end

      checklength(node.requireds.length, failing)

      parent_checking_type = checking_type
      @checking_type = true

      node.requireds.each_with_index do |required, index|
        pushindex(index)
        visit(required)
        pop
      end

      @checking_type = parent_checking_type
      jump(passing)
    end

    # in Prism::ConstantReadNode
    def visit_constant_path_node(node)
      checktype(constant_for(node), failing)
    end

    # in ConstantReadNode
    # in String
    def visit_constant_read_node(node)
      checktype(constant_for(node), failing)
    end

    # in InstanceVariableReadNode[name: Symbol]
    # in { name: Symbol }
    def visit_hash_pattern_node(node)
      constant = nil

      if node.constant
        constant = constant_for(node.constant)

        # We only support further deconstruction of hashes if they are prism
        # nodes. Otherwise we don't know how to make sense of them.
        unless constant < Node
          raise CompilationError, node.constant.inspect
        end

        visit(node.constant) if checking_type
      end

      parent_checking_type = checking_type

      # For each of the elements in the hash, we're going to push the field onto
      # the stack and then check its value.
      node.assocs.each do |assoc|
        @checking_type = true

        # We only support assoc nodes. The other option is a keyword splat node,
        # which doesn't make sense in this context.
        unless assoc.is_a?(AssocNode)
          raise CompilationError, assoc.inspect
        end

        # The only way to have a pattern matching key is for it to be a symbol.
        # So in this case we are safe to assume the interface.
        key = assoc.key.value.to_sym

        if (field = constant&.field(key))
          case field[:type]
          when :constant_list, :node_list
            if assoc.value.is_a?(ArrayPatternNode)
              @checking_type = false
              pushfield(key)
              visit(assoc.value)
              pop
            else
              raise IncompatibleFieldError.new("#{constant}##{key}", assoc.value.inspect)
            end
          else
            pushfield(key)
            visit(assoc.value)
            pop
          end
        else
          pushfield(key)
          visit(assoc.value)
          pop
        end
      end

      @checking_type = parent_checking_type
      jump(passing)
    end

    # This is effectively our entrypoint into the compiler since we always
    # compile one of these nodes as the top-level node in our expression.
    def visit_match_predicate_node(node)
      @passing = label
      @failing = label

      visit(node.pattern)

      pushlabel(@failing)
      fail

      pushlabel(@passing)
      @passing = nil
      @failing = nil

      optimize_jumps
      eliminate_unreachable
      link_labels
    end

    # in nil
    def visit_nil_node(node)
      checknil(failing)
    end

    # in 0..10
    def visit_range_node(node)
      bounds =
        [node.left, node.right].map do |bound|
          case bound
          when nil, NilNode
          when IntegerNode
            bound.value
          else
            raise CompilationError, node.inspect
          end
        end

      checkobject(Range.new(*bounds, node.exclude_end?), failing)
    end

    # in /abc/
    def visit_regular_expression_node(node)
      checkobject(Regexp.new(node.content, node.closing[1..]), failing)
    end

    # in "foo"
    def visit_string_node(node)
      checkobject(node.unescaped, failing)
    end

    # in :foo
    def visit_symbol_node(node)
      checkobject(node.value.to_sym, failing)
    end

    private

    # Return the constant that a node represents.
    def constant_for(node)
      # First, gather up all of the parts of the constant. This makes an array
      # of symbols representing each part.
      parts = []
      current = node

      while current.is_a?(ConstantPathNode)
        parts.unshift(current.child.name)
        current = current.parent
      end

      # Unshift the base constant onto the parts array. This is either going to
      # be a constant read or the implicit object base.
      parts.unshift(current.name) if current

      # Next, check if there's only one part and that it matches a prism
      # constant. We do this as a nice shortcut to allow you to specify a node
      # name without having to prefix it with Prism::.
      if parts.length == 1 && Prism.const_defined?(parts[0], false)
        return Prism.const_get(parts[0])
      end

      # Otherwise, attempt to check the constant path.
      current = Object
      parts.each do |part|
        if current.const_defined?(part, false)
          current = current.const_get(part)
        else
          raise NameError, parts.join("::")
        end
      end

      # Finally, return the constant that we found.
      current
    end

    # Disasm an object that could be a label or an offset.
    def disasm_label(insn)
      if insn.is_a?(Label)
        "%04d" % insn.pc
      else
        "%04d" % insn
      end
    end

    # Disasm a split hash.
    def disasm_split(split)
      pairs = split.map { |type, insn| "%s: %04d" % [type, insn.is_a?(Label) ? insn.pc : insn] }
      "{ #{pairs.join(", ")} }"
    end

    # Generic visit method for any kind of node.
    def visit(node)
      node&.accept(self)
    end

    ############################################################################
    # These methods are used to generate bytecode.                             #
    ############################################################################

    def checklength(length, label)
      insns.push(:checklength, length, label)
      label.push_jump(insns.length - 1)
    end

    def checknil(label)
      insns.push(:checknil, label)
      label.push_jump(insns.length - 1)
    end

    def checkobject(object, label)
      insns.push(:checkobject, object, label)
      label.push_jump(insns.length - 1)
    end

    def checktype(type, label)
      insns.push(:checktype, type, label)
      label.push_jump(insns.length - 1)
    end

    def fail
      insns.push(:fail)
    end

    def jump(label)
      insns.push(:jump, label)
      label.push_jump(insns.length - 1)
    end

    def label
      new_label = Label.new
      labels << new_label
      new_label
    end

    def opt_splittype(labels, label)
      insns.push(:opt_splittype, labels, label)
      labels.each { |type, type_label| type_label.push_split(insns.length - 2, type) }
      label.push_jump(insns.length - 1)
    end

    def pop
      insns.push(:pop)
    end

    def pushfield(name)
      insns.push(:pushfield, name)
    end

    def pushindex(index)
      insns.push(:pushindex, index)
    end

    def pushlabel(label)
      label.pc = insns.length
      insns.push(label)
    end

    ############################################################################
    # These methods are used to optimize/finalize bytecode.                    #
    ############################################################################

    # Iterate over each instruction in the bytecode.
    def each_insn(pc = 0)
      max_pc = insns.length

      while pc < max_pc
        insn = insns[pc]
        yield pc, insn

        case insn
        when :fail, :pop
          pc += 1
        when :checknil, :jump, :pushfield, :pushindex
          pc += 2
        when :checklength, :checkobject, :checktype, :opt_splittype
          pc += 3
        else
          pc += 1
        end
      end
    end

    # Make a pass over the labels to eliminate jump->jump sequences.
    def optimize_jumps
      labels.each do |label|
        current = label

        while insns[current.pc + 1] == :jump && insns[current.pc + 2] != current
          current = insns[current.pc + 2]
        end

        if current != label
          current.jumps.concat(label.jumps)
          label.jumps.each do |pc|
            insns[pc] = current
          end
          label.jumps.clear

          current.splits.concat(label.splits)
          label.splits.each do |(pc, type)|
            insns[pc][type] = current
          end
          label.splits.clear
        end
      end
    end

    # Eliminate all of the instructions that are unreachable.
    def eliminate_unreachable
      blocks = {}
      queue = [0]
      max_pc = insns.length

      # First, find the start of every basic block.
      while (pc = queue.shift)
        blocks[pc] = []

        each_insn(pc) do |pc, insn|
          case insn
          when :checknil
            queue << insns[pc + 1].pc
          when :checklength, :checkobject, :checktype
            queue << insns[pc + 2].pc
          when :fail
            break
          when :jump
            queue << insns[pc + 1].pc
            break
          when :opt_splittype
            queue.concat(insns[pc + 1].values.map(&:pc))
            queue << insns[pc + 2].pc
            break
          end
        end
      end

      # Next, find the end of every basic block, and set their instruction
      # lists.
      blocks.each do |pc, block|
        start_pc = pc
        end_pc = pc

        each_insn(start_pc) do |pc, insn|
          if pc != start_pc && blocks.key?(pc)
            end_pc = pc
            break
          end

          case insn
          when :jump
            end_pc = pc + 2
            break
          when :opt_splittype
            end_pc = pc + 3
            break
          end
        end

        block.concat(insns[start_pc...end_pc])
      end

      # Next, schedule the blocks and determine the mapping of old PCs to new
      # PCs so that we can properly update labels.
      insns.clear
      blocks = blocks.to_a.sort!

      labels.clear
      new_labels = {}

      blocks.each do |(old_pc, block)|
        new_labels[old_pc] = Label.new(insns.length) if old_pc != 0
        insns.concat(block)
      end

      # Now, we can update the labels to point to the correct PCs.
      labels.concat(new_labels.values)

      each_insn do |pc, insn|
        case insn
        when :checknil, :jump
          new_labels.fetch(insns[pc + 1].pc).push_jump(pc + 1)
          insns[pc + 1] = new_labels.fetch(insns[pc + 1].pc)
        when :checklength, :checkobject, :checktype
          new_labels.fetch(insns[pc + 2].pc).push_jump(pc + 2)
          insns[pc + 2] = new_labels.fetch(insns[pc + 2].pc)
        when :opt_splittype
          split = insns[pc + 1]
          split.each do |type, old_label|
            new_labels.fetch(old_label.pc).push_split(pc + 1, type)
            split[type] = new_labels.fetch(old_label.pc)
          end

          new_labels.fetch(insns[pc + 2].pc).push_jump(pc + 2)
          insns[pc + 2] = new_labels.fetch(insns[pc + 2].pc)
        end
      end
    end

    # Replace all of the labels in the bytecode with their corresponding PCs.
    def link_labels
      # First, we'll group the labels by PC, then transform the PCs into their
      # new PCs.
      new_labels = {}
      labels.group_by(&:pc).to_a.sort!.each_with_index do |(old_pc, labels), index|
        new_pc = old_pc - index
        labels.each { |label| new_labels[label] = new_pc }
      end

      # Next, we need to go back and patch the instructions where we should be
      # jumping to labels to point to the correct PC.
      labels.each do |label|
        label.jumps.each do |pc|
          insns[pc] = new_labels[label]
        end

        label.splits.each do |(pc, type)|
          insns[pc][type] = new_labels[label]
        end
      end

      # Finally, we can remove all of the labels from the list of
      # instructions.
      insns.reject! { |insn| insn.is_a?(Label) }
    end
  end
end
