from aeon.ast import *
from aeon.types import *

def deduce(ast, context, holed):

    for declaration, holes in holed:
        deducer = HoleDeducer(context, holes)
        deducer.deduce(declaration)

    return ast, context, holed

# =============================================================================
# Hole Deducer
class HoleDeducer():
    def __init__(self, context, holes):

        self.context = context
        self.holes = holes

        self.counter = 0
        self.hole_stack = list()

    def deduce_hole(self, node):
        node.type = self.hole_stack[-1]
        del (self.hole_stack[-1])
        
    def deduce_definition(self, node: Definition):
        self.hole_stack.append(node.return_type)
        self.deduce(node.body)

    def deduce_literal(self, node: Literal):
        # Does nothing
        pass

    def deduce_var(self, node: Var):
        # Does nothing
        pass
        
    def deduce_if(self, node: If):

        # Try to deduce the condition
        if node.cond.type is bottom:
            self.hole_stack.append(t_b)
        
        self.deduce(node.cond)
        
        # If the otherwise is a hole
        if node.otherwise.type is bottom:
            self.hole_stack.append(node.type)
        
        self.deduce(node.then)

        # If the then is a hole
        if node.then.type is bottom:
            self.hole_stack.append(node.type)
        
        self.deduce(node.otherwise)

    def deduce_application(self, node: Application):
        if isinstance(node.target, Abstraction):
            self.hole_stack.append(node.target.arg_type)
        else:
            pass
        self.visit(node.target)
        self.visit(node.argument)

    def deduce_abstraction(self, node: Abstraction):
        self.visit(node.body)

    def deduce_tabstraction(self, node: TAbstraction):
        pass

    def deduce_tapplication(self, node: TApplication):
        pass

    def deduce(self, node):
        if isinstance(node, Program):
            self.visitProgram(node)
        elif isinstance(node, Hole):
            self.visitHole(node)
        elif isinstance(node, Literal):
            self.visitLiteral(node)
        elif isinstance(node, Var):
            self.visitVar(node)
        elif isinstance(node, If):
            self.visitIf(node)
        elif isinstance(node, Application):
            self.visitApplication(node)
        elif isinstance(node, Abstraction):
            self.visitAbstraction(node)
        elif isinstance(node, Definition):
            self.visitDefinition(node)
        elif isinstance(node, TypeAlias):
            self.visitTypeAlias(node)
        elif isinstance(node, TAbstraction):
            self.visitTAbstraction(node)
        elif isinstance(node, TApplication):
            self.visitTApplication(node)
        else:
            raise Exception("Unknown type of node: ", type(node))


'''

program(x : Integer, y : Double) :: String {
    ??   ~~~~~> T1 : * => ?T1?;
    ??(??) ~~~> T1 : * => T2 : * => ?T1?(?T2?)
    ??[String](??) ~~~> T1 : * -> * => T2 : * => ?T1?(?T2?)
    
}

'''