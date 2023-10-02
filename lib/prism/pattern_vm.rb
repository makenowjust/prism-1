# frozen_string_literal: true

module Prism
  class PatternVM
    class Compiler < BasicVisitor
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
        attr_reader :pcs, :splits

        def initialize
          @pcs = []
          @splits = []
        end

        def push_pc(pc)
          pcs << pc
        end

        def push_split(pc, type)
          splits << [pc, type]
        end
      end

      attr_reader :vm, :passing, :failing
  
      def initialize(vm)
        @vm = vm
        @passing = nil
        @failing = nil
      end

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
            labels = groups.transform_values { Label.new }
            vm.splittype(labels, failing)

            groups.each do |type, clauses|
              vm.pushlabel(labels[type])

              if clauses.length > 1
                parent_failing = failing

                clauses.each do |clause|
                  @failing = Label.new
                  visit(clause)
                  vm.jump(passing)
                  vm.pushlabel(@failing)
                end

                @failing = parent_failing
              else
                visit(clauses.first)
                vm.jump(passing)
              end
            end

            return
          end
        else
          parent_failing = failing
          @failing = Label.new

          visit(node.left)
          vm.jump(passing)

          vm.pushlabel(@failing)
          @failing = parent_failing
          visit(node.right)

          vm.jump(passing)
        end
      end

      # in [foo, bar, baz]
      def visit_array_pattern_node(node)
        compile_error(node) if node.constant || !node.rest.nil? || node.posts.any?
  
        vm.checktype(Array, failing)
        vm.checklength(node.requireds.length, failing)
  
        node.requireds.each_with_index do |required, index|
          vm.pushindex(index)
          visit(required)
          vm.pop
        end
  
        vm.jump(passing)
      end
  
      # name: Symbol
      def visit_assoc_node(node)
        if node.key.is_a?(Prism::SymbolNode)
          vm.pushfield(node.key.value.to_sym)
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
          vm.checktype(Prism.const_get(value), failing)
        elsif Object.const_defined?(value, false)
          vm.checktype(Object.const_get(value), failing)
        else
          compile_error(node)
        end
      end
  
      # in InstanceVariableReadNode[name: Symbol]
      # in { name: Symbol }
      def visit_hash_pattern_node(node)
        visit(node.constant) if node.constant
  
        node.assocs.each do |assoc|
          visit(assoc)
          vm.pop
        end
  
        vm.jump(passing)
      end
  
      # foo in bar
      def visit_match_predicate_node(node)
        @passing = Label.new
        @failing = Label.new

        visit(node.pattern)

        vm.pushlabel(@failing)
        vm.fail

        vm.pushlabel(@passing)
        @passing = nil
        @failing = nil
      end

      private
  
      def compile_error(node)
        raise CompilationError, node.inspect
      end
    end

    attr_reader :insns

    def initialize(pattern)
      @insns = []
      Prism.parse("nil in #{pattern}").value.statements.body.first.accept(Compiler.new(self))
    end

    def disasm
      output = +""
      pc = 0

      while pc < insns.length
        case (insn = insns[pc])
        when :checklength
          output << "%04d %-12s %d, %04d\n" % [pc, insn, insns[pc + 1], insns[pc + 2]]
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

    def checklength(length, label)
      insns.push(:checklength, length, -1)
      label.push_pc(insns.length - 1)
    end

    def checktype(type, label)
      insns.push(:checktype, type, -1)
      label.push_pc(insns.length - 1)
    end

    def fail
      insns.push(:fail)
    end

    def jump(label)
      insns.push(:jump, -1)
      label.push_pc(insns.length - 1)
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
      label.pcs.each do |pc|
        insns[pc] = insns.length
      end

      label.splits.each do |(pc, type)|
        insns[pc][type] = insns.length
      end
    end

    def splittype(labels, label)
      insns.push(:splittype, labels, label)
      labels.each { |type, type_label| type_label.push_split(insns.length - 2, type) }
      label.push_pc(insns.length - 1)
    end
  end
end
