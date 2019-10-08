from .ast import *
from .types import *
from .substitutions import *
from .synthesis import *
from .zed import *
from .stdlib import initial_context

def infereTypes(ast):
     
    ctx = {}
    
    for x in initial_context:
        if type(initial_context.get(x)[0]) is Definition:
            ctx[x] = initial_context.get(x)[0].type

    synth = TypeInferer(ctx)
    synth.visit(ast)

# =============================== Synthesizer ===============================
class TypeInferer():
    def __init__(self, ctx):
        self.ctx = ctx
        self.counter = 0

        self.hole_stack = set()

    def visitProgram(self, node:Program):
        for x in node.declarations:
            self.visit(x)

    def visitHole(self, node:Hole):
        pass
    
    def visitLiteral(self, node:Literal):
        pass

    def visitVar(self, node:Var):
        if node.type is None:
            node.type = self.ctx.get(node.name)
            self.ctx[node.name] = node.type 
        
    def visitIf(self, node:If):

        # Visit the condition, then and else statements
        self.visit(node.cond)
        self.visit(node.then)
        self.visit(node.otherwise)

        node.type = self.leastCommonSupertype(node)

    def visitApplication(self, node:Application):

        # Visit the target and argument
        self.visit(node.target)

        # Prevent redefinitions of abstractions in function body
        oldContext = self.ctx.copy()
        self.ctx = self.ctx.copy()
        self.visit(node.argument)
        self.ctx = oldContext

        # The type of the argument of the abstraction, is the type of the argument of the application
        if type(node.target) is Abstraction:
            # Define the type of the arguments of the abstraction
            node.target.arg_type = node.argument.type
            
            # The type of the target of current node is the result of the abstraction
            if type(node.target.type) is AbstractionType:
                node.type = node.target.type.return_type
            else:
                node.type = node.target.type
        else:
            if type(node.target.type) is AbstractionType:
                node.type = node.target.type.return_type
            else:
                node.type = node.target.type     
        return node.type

    def visitAbstraction(self, node:Abstraction):
        self.ctx[node.arg_name.name] = node.arg_type
        self.visit(node.body)
        node.type = AbstractionType(node.arg_name, node.arg_type, node.body.type)

        self.ctx[node.arg_name.name] = node.arg_type
        
    def visitDefinition(self, node:Definition):

        # Add the current var to the context
        self.ctx[node.name] = node.type  

        oldContext = self.ctx
        self.ctx = self.ctx.copy()
        self.visit(node.body)
        self.ctx = oldContext
    
    def visitTAbstraction(self, node:TAbstraction):
        self.visit(node.body)
    
    def visitTApplication(self, node:TApplication):
        self.visit(node.body)

    def visitTypeAlias(self, node:TypeAlias):
        pass
    
    def visitTypeDeclaration(self, node:TypeDeclaration):
        pass

    def visitImport(self, node:Import):
        pass

    def visit(self, node):
        if type(node) is Program:
            self.visitProgram(node)
        elif type(node) is Hole:
            self.visitHole(node)
        elif type(node) is Literal:
            self.visitLiteral(node)
        elif type(node) is Var:
            self.visitVar(node)
        elif type(node) is If:
            self.visitIf(node)
        elif type(node) is Application:
            self.visitApplication(node)
        elif type(node) is Abstraction:
            self.visitAbstraction(node)
        elif type(node) is Definition:
            self.visitDefinition(node)
        elif type(node) is TypeAlias:
            self.visitTypeAlias(node)
        elif type(node) is TypeDeclaration:
            self.visitTypeDeclaration(node)
        elif type(node) is TAbstraction:
            self.visitTAbstraction(node)
        elif type(node) is TApplication:
            self.visitTApplication(node)
        elif type(node) is Import:
            self.visitImport(node)
        else:
            print("Unknown type of node: ", type(node))

# ============================= Help Functions =============================
    # TODO: leastCommon = leastCommonSupertype(typeThen, typeElse)
    def leastCommonSupertype(self, node:If):

        result = node.then.type

        if type(node.then.type) is BasicType:
            result = node.then.type
        elif type(node.then.type) is RefinedType:
            if type(node.otherwise.type) is BasicType:
                result = node.otherwise.type
            elif type(node.otherwise.type) is RefinedType:
                result = RefinedType(node.then.type.name, node.then.type, Application(Application('And', node.otherwise.type.cond), node.then.type.cond))
            elif type(node.otherwise.type) is AbstractionType:
                # TODO: LCS
                pass
        elif type(node.then.type) is AbstractionType:
            pass
        else:
            print("ERROR: While trying to evaluate leastCommonSupertype")
        return result


    def nextVoidVar(self):
        result = '_infer{}'.format(self.counter)
        self.counter += 1
        return result