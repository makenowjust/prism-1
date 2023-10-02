# frozen_string_literal: true

module Prism
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

    class Label
      attr_reader :jumps, :splits

      def initialize
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

    attr_reader :pattern
    attr_reader :insns, :labels
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

    def or(other)
      PatternVM.new("#{pattern} | #{other.pattern}")
    end
    alias | or

    def compile
      visit(Prism.parse("nil in #{pattern}").value.statements.body.first)
    end

    def disasm
      output = +""
      pc = 0

      while pc < insns.length
        case (insn = insns[pc])
        when :checklength
          output << "%04d %-12s %d, %04d\n" % [pc, insn, insns[pc + 1], insns[pc + 2]]
          pc += 3
        when :checknil
          output << "%04d %-12s %04d\n" % [pc, insn, insns[pc + 1]]
          pc += 2
        when :checkobject
          output << "%04d %-12s %s, %04d\n" % [pc, insn, insns[pc + 1].inspect, insns[pc + 2]]
          pc += 3
        when :checktype
          output << "%04d %-12s %s, %04d\n" % [pc, insn, insns[pc + 1], insns[pc + 2]]
          pc += 3
        when :fail
          output << "%04d %-12s\n" % [pc, insn]
          pc += 1
        when :jump
          output << "%04d %-12s %04d\n" % [pc, insn, insns[pc + 1]]
          pc += 2
        when :pushfield
          output << "%04d %-12s %s\n" % [pc, insn, insns[pc + 1]]
          pc += 2
        when :pushindex
          output << "%04d %-12s %d\n" % [pc, insn, insns[pc + 1]]
          pc += 2
        when :pop
          output << "%04d %-12s\n" % [pc, insn]
          pc += 1
        when :splittype
          output << "%04d %-12s %s, %04d\n" % [pc, insn, insns[pc + 1].inspect, insns[pc + 2]]
          pc += 3
        else
          raise "Unknown instruction: #{insn.inspect}"
        end
      end

      output
    end

    def run(node)
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
            pc += 2
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
        when :pushfield
          stack.push(stack[-1].public_send(insns[pc + 1]))
          pc += 2
        when :pushindex
          stack.push(stack[-1][insns[pc + 1]])
          pc += 2
        when :pop
          stack.pop
          pc += 1
        when :splittype
          pc = insns[pc + 1].fetch(stack[-1].type, insns[pc + 2])
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
      # nodes. This will let us do further optimizations if there are more
      # than 2.
      clauses = [node.left, node.right]
      while clauses.first.is_a?(AlternationPatternNode)
        clause = clauses.shift
        clauses.unshift(clause.left, clause.right)
      end

      # Next, we're going to check on the kinds of patterns that we're trying
      # to compile. If it's possible to take advantage of checking the type
      # only once, then we will do that.
      groups =
        clauses.group_by do |clause|
          constant =
            case clause.type
            when :array_pattern_node, :find_pattern_node, :hash_pattern_node
              clause.constant
            when :constant_read_node, :constant_path_node
              clause
            end

          if constant
            parts = []
            while constant.is_a?(ConstantPathNode)
              parts.unshift(constant.child.name)
              constant = constant.parent
            end
            parts.unshift(constant&.name)
          else
            :ungrouped
          end
        end

      # If we have more than one group, we can do a special optimization where
      # we check the type once and then jump to the correct clause.
      if !groups.key?(:ungrouped) && groups.length > 1
        # Next, transform the keys from constant paths to prism types so that
        # we can use the .type method to switch effectively.
        groups.transform_keys! do |path|
          if ((path.length == 1) || (path.length == 2 && path[0] == :Prism)) && Prism.const_defined?(path.last, false)
            Prism.const_get(path.last).type
          else
            path
          end
        end

        # If we found a node type for every group, then we will perform our
        # optimization.
        if groups.keys.none? { |key| key.is_a?(Array) }
          labels = groups.transform_values { label }
          splittype(labels, failing)

          groups.each do |type, clauses|
            pushlabel(labels[type])

            parent_failing = failing
            parent_checking_type = checking_type
            @checking_type = false

            last_index = clauses.length - 1
            clauses.each_with_index do |clause, index|
              @failing = label if index != last_index

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

          return
        end
      else
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
      compile_error(node) if node.constant || !node.rest.nil? || node.posts.any?

      checktype(Array, failing) if checking_type
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

    # name: Symbol
    def visit_assoc_node(node)
      if node.key.is_a?(Prism::SymbolNode)
        pushfield(node.key.value.to_sym)
        visit(node.value)
      else
        compile_error(node)
      end
    end

    # in Prism::ConstantReadNode
    def visit_constant_path_node(node)
      parent = node.parent

      if parent.is_a?(ConstantReadNode) && parent.slice == "Prism"
        visit(node.child)
      else
        compile_error(node)
      end
    end

    # in ConstantReadNode
    # in String
    def visit_constant_read_node(node)
      value = node.slice

      if Prism.const_defined?(value, false)
        checktype(Prism.const_get(value), failing)
      elsif Object.const_defined?(value, false)
        checktype(Object.const_get(value), failing)
      else
        compile_error(node)
      end
    end

    # in InstanceVariableReadNode[name: Symbol]
    # in { name: Symbol }
    def visit_hash_pattern_node(node)
      constant = nil
      if node.constant
        constant = constant_for(node.constant)
        visit(node.constant) if checking_type
      end

      parent_checking_type = checking_type
      node.assocs.each do |assoc|
        @checking_type = true

        if assoc.is_a?(AssocNode)
          key = assoc.key.value.to_sym

          field = constant.field(key)
          if field
            case field[:type]
            when :node_list
              if assoc.value.is_a?(ArrayPatternNode)
                @checking_type = false
                visit(assoc)
                pop
              else
                compile_error(assoc.value)
              end
            else
              visit(assoc)
              pop
            end
          else
            compile_error(assoc.key)
          end
        else
          compile_error(assoc)
        end
      end

      @checking_type = parent_checking_type
      jump(passing)
    end

    # foo in bar
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
      link_labels
    end

    # in nil
    def visit_nil_node(node)
      checknil(failing)
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

    # Raise an error when we encounter a node that we don't know how to compile.
    def compile_error(node)
      raise CompilationError, node.inspect
    end

    # Return the constant that a node represents.
    def constant_for(node)
      parts = []
      while node.is_a?(ConstantPathNode)
        parts.unshift(node.child.name)
        node = node.parent
      end
      parts.unshift(node&.name || :Object)

      case parts.length
      when 1
        if Prism.const_defined?(parts[0], false)
          Prism.const_get(parts[0])
        else
          compile_error(node)
        end
      when 2
        if parts[0] == :Prism && Prism.const_defined?(parts[1], false)
          Prism.const_get(parts[1])
        else
          compile_error(node)
        end
      when 3
        if parts[0] == :Object && parts[1] == :Pattern && Prism.const_defined?(parts[2], false)
          Prism.const_get(parts[2])
        else
          compile_error(node)
        end
      else
        compile_error(node)
      end
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
      insns.push(label)
    end

    def splittype(labels, label)
      insns.push(:splittype, labels, label)
      labels.each { |type, type_label| type_label.push_split(insns.length - 2, type) }
      label.push_jump(insns.length - 1)
    end

    ############################################################################
    # These methods are used to optimize/finalize bytecode.                    #
    ############################################################################

    # Accept a label and find the label that it should actually be jumping to
    # in case of a jump->jump sequence.
    def follow_jump(label)
      index = insns.index(label)

      if insns[index + 1] == :jump
        follow_jump(insns[index + 2])
      else
        label
      end
    end

    # Accepts a PC that refers to a label and finds the label that it should
    # actually be jumping to in case of a jump->jump sequence.
    def optimize_jump(pc)
      old_label = insns[pc]
      new_label = follow_jump(old_label)

      if old_label != new_label
        old_label.jumps.delete(pc)
        new_label.jumps.push(pc)
        insns[pc] = new_label
      end
    end

    # Accepts a PC that refers to a split label hash and finds the labels that
    # they should actually be jumping to in case of a jump->jump sequence.
    def optimize_split(pc)
      split = insns[pc]
      split.each do |type, old_label|
        new_label = follow_jump(old_label)

        if old_label != new_label
          key = [pc, type]

          old_label.splits.delete(key)
          new_label.splits.push(key)

          split[type] = new_label
        end
      end
    end

    # Make a pass over the instructions to eliminate jump->jump sequences.
    def optimize_jumps
      pc = 0
      max_pc = insns.length

      while pc < max_pc
        case insns[pc]
        when :fail, :pop
          pc += 1
        when :jump
          optimize_jump(pc + 1)
          pc += 2
        when :pushfield, :pushindex
          pc += 2
        when :checklength, :checknil, :checkobject, :checktype
          optimize_jump(pc + 1)
          pc += 3
        when :splittype
          optimize_split(pc + 1)
          optimize_jump(pc + 2)
          pc += 3
        else
          pc += 1
        end
      end
    end

    def link_labels
      # First, we need to find all of the PCs in the list of instructions and
      # track where they are to find their current PCs.
      pc = 0
      max_pc = insns.length

      pcs = {}
      while pc < max_pc
        case (insn = insns[pc])
        when :fail, :pop
          pc += 1
        when :jump, :pushfield, :pushindex
          pc += 2
        when :checklength, :checknil, :checkobject, :checktype, :splittype
          pc += 3
        else
          if insn.is_a?(Label)
            (pcs[pc] ||= []) << insn
            pc += 1
          else
            raise "Unknown instruction: #{insn.inspect}"
          end
        end
      end

      # Next, we need to find their new PCs by accounting for them being
      # removed from the list of instructions.
      pcs.transform_keys!.with_index do |key, index|
        key - index
      end

      # Next, set up the new list of labels to point to the correct PCs.
      pcs = pcs.each_with_object({}) do |(pc, labels), result|
        labels.each do |label|
          result[label] = pc
        end
      end

      # Next, we need to go back and patch the instructions where we should be
      # jumping to labels to point to the correct PC.
      labels.each do |label|
        label.jumps.each do |pc|
          insns[pc] = pcs[label]
        end

        label.splits.each do |(pc, type)|
          insns[pc][type] = pcs[label]
        end
      end

      # Finally, we can remove all of the labels from the list of
      # instructions.
      insns.reject! { |insn| insn.is_a?(Label) }
    end
  end
end
