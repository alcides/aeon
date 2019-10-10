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

    TypeInferer(ctx).visit(ast)
    HoleInferer(ctx).visit(ast)

# =============================== Type Inferer ===============================
class TypeInferer():
    def __init__(self, ctx):
        self.ctx = ctx
        self.counter = 0

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
        if type(node.target) is Abstraction and node.target.arg_type is None:
            # Define the type of the arguments of the abstraction
            node.target.arg_type = node.argument.type
            node.target.arg_name.type = node.argument.type
            
        # The type of the target of current node is the result of the abstraction
        if type(node.target.type) is AbstractionType:
            node.type = node.target.type.return_type
        else:
            node.type = node.target.type     

    def visitAbstraction(self, node:Abstraction):
        self.ctx[node.arg_name.name] = node.arg_type
        self.visit(node.body)
        node.type = AbstractionType(node.arg_name, node.arg_type, node.body.type)
        self.ctx[node.arg_name.name] = node.arg_type
        node.arg_name.type = node.arg_type
        
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

        if node.then.type is None or node.otherwise.type is None:
            return None

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



# =============================== Hole Inferer ===============================
class HoleInferer():
    def __init__(self, ctx):
        self.ctx = ctx
        self.counter = 0
        self.hole_stack = list()

    def visitProgram(self, node:Program):
        for x in node.declarations:
            self.visit(x)

    def visitHole(self, node:Hole):
        if node.type is None and self.hole_stack:
            node.type = self.hole_stack[-1]
            del(self.hole_stack[-1])
        else:
            if not self.hole_stack:
                print("The hole stack is empty")
    
    def visitLiteral(self, node:Literal):
        pass

    def visitVar(self, node:Var):
        pass
        
    def visitIf(self, node:If):
        
        # Visit the condition, then and else statements
        if node.cond.type is None:
            self.hole_stack.append(t_b)
            self.visit(node.cond)

        # Both then and otherwise have a hole
        if node.then.type is None and node.otherwise.type is None:
            self.hole_stack.append(self.hole_stack[-1])
            self.visit(node.then)
            self.visit(node.otherwise)
            node.type = node.then.type  # Both then and otherwise have the same types
        # Then is None
        elif node.then.type is None:
            if len(self.hole_stack) > 1:
                self.hole_stack.append(RefinedType(self.nextVoidVar(), node.otherwise.type, node.cond))
            self.visit(node.then)
            node.type = getBasicType(node.otherwise.type) # TODO: Give the most general type
        # Else is None
        else:
            if len(self.hole_stack) > 1:
                typee = RefinedType(self.nextVoidVar(), node.then.type, Application(Var('not'), node.cond))
                self.hole_stack.append(typee)
            self.visit(node.otherwise)
            node.type = getBasicType(node.then.type) # TODO: Give the most general type

    def visitApplication(self, node:Application):
  
        # I am on a possible hole application case
        if type(node.target) is not Abstraction:
            if node.argument.type is not None:
                arg_type = node.argument.type
            elif len(self.hole_stack) > 1:
                arg_type = self.hole_stack[-1]
            else:
                arg_type = t_t
            typee = AbstractionType(self.nextVoidVar(), arg_type, self.hole_stack[-1])
            self.hole_stack.append(typee)
            self.visit(node.target)
            if typee in self.hole_stack:
                self.hole_stack.remove(typee)
        else:
            self.visit(node.target.body) # Passar a frente o Abstraction

        oldContext = self.ctx.copy()
        self.ctx = self.ctx.copy()

        if type(node.target) is Abstraction:
            if node.target.type.arg_type is None:
                tee = t_t
            else:
                tee = node.target.type.arg_type
        # Var or Application
        else:
            tee = node.target.type.arg_type 

        self.hole_stack.append(tee)
        self.visit(node.argument)
        
        if tee in self.hole_stack:
            self.hole_stack.remove(tee)
        
        self.ctx = oldContext

        # The type of the argument of the abstraction, is the type of the argument of the application
        if type(node.target) is Abstraction and node.target.arg_name.name.startswith('_'):
            # Define the type of the arguments of the abstraction
            node.target.arg_type = node.argument.type
            node.target.arg_name.type = node.argument.type
            
        # The type of the target of current node is the result of the abstraction
        if type(node.target.type) is AbstractionType:
            node.type = node.target.type.return_type
        else:
            node.type = node.target.type     

    def visitAbstraction(self, node:Abstraction):
        
        self.ctx[node.arg_name.name] = node.arg_type
        # For sure this contains a type
        if node.arg_type is None:
            print(">"*20, "Opsie, visitAbstraction in hole inferer")    
    
        self.visit(node.body)

        if node.arg_type in self.hole_stack:
            self.hole_stack.remove(node.arg_type)
        
        node.type = AbstractionType(node.arg_name, node.arg_type, node.body.type)
        self.ctx[node.arg_name.name] = node.arg_type


        
    def visitDefinition(self, node:Definition):

        # Add the current var to the context
        self.ctx[node.name] = node.type  

        oldContext = self.ctx

        bodyNode, typee = self.getBodyAndReturnType(node)
        
        self.hole_stack = list()
        self.hole_stack.append(typee)
        
        self.ctx = self.ctx.copy()
        self.visit(bodyNode)
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

    def nextVoidVar(self):
        result = '_infer{}'.format(self.counter)
        self.counter += 1
        return result

    def getBodyAndReturnType(self, node:Definition):

        typee = node.type

        # Strip off the typebastractions
        while type(typee) is TypeAbstraction:
            typee = typee.type

        abstCounter = 0

        # Strip off the abstraction types
        while type(typee) is AbstractionType:
            typee = typee.return_type
            abstCounter += 1

        node = node.body

        # Get the body of the function
        while type(node) is TAbstraction:
            node = node.body
        while abstCounter > 0:
            node = node.body
            abstCounter -= 1
        
        return node, typee

def getBasicType(typee):

    if type(typee) is BasicType:
        return typee
    elif type(typee) is RefinedType:
        return getBasicType(typee.type)
    elif type(typee) is AbstractionType:
        # return getBasicType(type.)
        pass
    return typee # TODO: