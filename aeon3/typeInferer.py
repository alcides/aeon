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

    HoleInferer(ctx).visit(ast)

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
        self.hole_stack.append(t_b)
        self.visit(node.cond)

        if t_b in self.hole_stack:
            self.hole_stack.remove(t_b)

        # Both then and otherwise have a hole
        if node.then.type is None and node.otherwise.type is None:
            self.hole_stack.append(self.hole_stack[-1])
            self.visit(node.then)
            self.visit(node.otherwise)
            node.type = node.then.type  # Both then and otherwise have the same types
        # Then is None
        elif node.then.type is None:
            if len(self.hole_stack) > 1:
                void_var = Var(self.nextVoidVar(), node.otherwise.type)
                self.hole_stack.append(RefinedType(self.nextVoidVar(), node.otherwise.type, node.cond))
            self.visit(node.then)
            node.type = getBasicType(node.otherwise.type) # TODO: Give the most general type
            self.visit(node.otherwise)
        # Else is None
        elif node.otherwise.type is None:
            if len(self.hole_stack) > 1:
                typee = RefinedType(self.nextVoidVar(), node.then.type, Application(Var('!'), node.cond))
                self.hole_stack.append(typee)
            self.visit(node.otherwise)
            node.type = getBasicType(node.then.type) # TODO: Give the most general type
            self.visit(node.then)
        # There may be an hole in the middle of the if or else, so we revisit the tree
        else:
            self.visit(node.then)
            self.visit(node.otherwise)


    def visitApplication(self, node:Application):
  
        # I am on a possible hole application case
        if type(node.target) is not Abstraction:
            if node.argument.type is not None:
                arg_type = node.argument.type
            elif len(self.hole_stack) > 1:
                arg_type = self.hole_stack[-1]
            else:
                arg_type = t_t
            typee = AbstractionType(Var(self.nextVoidVar()), arg_type, self.hole_stack[-1])
            self.hole_stack.append(typee)
            self.visit(node.target)
            if typee in self.hole_stack:
                self.hole_stack.remove(typee)
        else:
            self.visit(node.target.body) # Passar a frente o Abstraction

        oldContext = self.ctx.copy()
        self.ctx = self.ctx.copy()
        
        if type(node.target) is Abstraction:
            tee = t_t
        elif type(node.target) is Var:
            tee = node.target.type 
        elif type(node.target) is Application:
            tee = node.target.type
        elif type(node.target) is TApplication:
            tee = node.target.type
        elif type(node.target) is Hole:
            tee = node.target.type.arg_type
        else:
            print("It happened", node, type(node.target))
            tee = node.target.type

        if type(tee) is TypeAbstraction:
            tempTee = node.target.type
            while type(tempTee.type) is TypeAbstraction:
                tempTee = tempTee.type
            tempTee.type = tempTee.type.return_type if type(tempTee.type) is AbstractionType else tempTee.type
            
        self.hole_stack.append(tee)
        self.visit(node.argument)
        
        if tee in self.hole_stack:
            self.hole_stack.remove(tee)
        
        self.ctx = oldContext

        # The type of the argument of the abstraction, is the type of the argument of the application
        if type(node.target) is Abstraction and (node.target.arg_type is None or node.target.arg_name.name.startswith('_')):
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
        
        node.type = AbstractionType(node.arg_name, node.arg_type, node.body.type)
        
        self.ctx[node.arg_name.name] = node.arg_type


        
    def visitDefinition(self, node:Definition):

        # Add the current var to the context
        self.ctx[node.name] = node.type  

        oldContext = self.ctx

        bodyNode, typee = getBodyAndReturnType(node)
        
        self.hole_stack = list()

        self.hole_stack.append(typee)
        self.ctx = self.ctx.copy()
        
        # Visit the body node
        self.visit(bodyNode)

        self.ctx = oldContext
        self.counter = 0

    def visitTAbstraction(self, node:TAbstraction):
        self.visit(node.body)
    
    def visitTApplication(self, node:TApplication):
        self.visit(node.target)

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

def getBodyAndReturnType(node:Definition):

    typee = node.type
    return_type = node._function_return_typee

    # Strip off the typebastractions
    while type(typee) is TypeAbstraction:
        typee = typee.type

    # Strip off the TAbstraction
    while type(node) is TAbstraction:
        node = node.body

    # Strip off the function parameters
    while typee != return_type:
        typee = typee.return_type
        node = node.body

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