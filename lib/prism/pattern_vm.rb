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
        attr_reader :pcs

        def initialize
          @pcs = []
        end

        def <<(pc)
          pcs << pc
        end
      end

      attr_reader :vm, :passing, :failing
  
      def initialize(vm)
        @vm = vm
        @passing = nil
        @failing = nil
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
        else
          binding.irb
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
        end
      end

      true
    end

    def checklength(length, label)
      insns.push(:checklength, length, -1)
      label << insns.length - 1
    end

    def checktype(type, label)
      insns.push(:checktype, type, -1)
      label << insns.length - 1
    end

    def fail
      insns.push(:fail)
    end

    def jump(label)
      insns.push(:jump, -1)
      label << insns.length - 1
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
    end
  end
end
