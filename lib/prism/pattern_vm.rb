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
  
      attr_reader :vm
  
      def initialize(vm)
        @vm = vm
      end
  
      # in [foo, bar, baz]
      def visit_array_pattern_node(node)
        compile_error(node) if node.constant || !node.rest.nil? || node.posts.any?
  
        vm.checktype(Array)
        vm.checklength(node.requireds.length)
  
        node.requireds.each_with_index do |required, index|
          vm.pushindex(index)
          visit(required)
          vm.pop
        end
  
        vm.match
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
          vm.checktype(Prism.const_get(value))
        elsif Object.const_defined?(value, false)
          vm.checktype(Object.const_get(value))
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
  
        vm.match
      end
  
      private
  
      def compile_error(node)
        raise CompilationError, node.inspect
      end
    end

    attr_reader :insns

    def initialize(pattern)
      @insns = []
      Prism.parse("nil in #{pattern}").value.statements.body.first.pattern.accept(Compiler.new(self))
    end

    def run(node)
      stack = [node]
      pc = 0

      while (insn = insns[pc])
        case insn
        when :checklength
          break unless stack[-1].length == insns[pc + 1]
          pc += 2
        when :checktype
          break unless stack[-1].is_a?(insns[pc + 1])
          pc += 2
        when :pushfield
          stack.push(stack[-1].public_send(insns[pc + 1]))
          pc += 2
        when :pushindex
          stack.push(stack[-1][insns[pc + 1]])
          pc += 2
        when :pop
          stack.pop
          pc += 1
        when :match
          return true
        end
      end

      false
    end

    def checklength(length)
      insns.push(:checklength, length)
    end

    def checktype(type)
      insns.push(:checktype, type)
    end

    def match
      insns.push(:match)
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
  end
end
