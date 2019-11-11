from .ast import Var, Literal, Definition, TypeAlias, TypeDeclaration, Program, Import, Abstraction, Application, If, Hole, TAbstraction, TApplication
from .types import Type, BasicType, AbstractionType, RefinedType, TypeApplication, TypeAbstraction, Kind, star, bottom, t_v, t_i, t_f, t_b, t_s, top
from .typechecker.substitutions import *
from .typechecker.zed import *
from .typechecker.typing import synth_type

from .synthesis import *
from .libraries.stdlib import initial_context


def inferTypes(ast):

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

    def visitProgram(self, node: Program):
        for x in node.declarations:
            self.visit(x)

    def visitHole(self, node: Hole):
        if node.type is None and self.hole_stack:
            node.type = self.hole_stack[-1]
            del (self.hole_stack[-1])
        else:
            if not self.hole_stack:
                print("The hole stack is empty")

    def visitLiteral(self, node: Literal):
        pass

    def visitVar(self, node: Var):
        pass

    def visitIf(self, node: If):

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
                void_var = Var(self.nextVoidVar()).with_type(
                    node.otherwise.type)
                self.hole_stack.append(
                    RefinedType(self.nextVoidVar(), node.otherwise.type,
                                node.cond))
            self.visit(node.then)
            node.type = self.returnBasicTypee(
                node.otherwise.type)  # TODO: Give the most general type
            self.visit(node.otherwise)
        # Else is None
        elif node.otherwise.type is None:
            if len(self.hole_stack) > 1:
                typee = RefinedType(self.nextVoidVar(), node.then.type,
                                    Application(Var('!'), node.cond))
                self.hole_stack.append(typee)
            self.visit(node.otherwise)
            node.type = self.returnBasicTypee(
                node.then.type)  # TODO: Give the most general type
            self.visit(node.then)
        # There may be an hole in the middle of the if or else, so we revisit the tree
        else:
            self.visit(node.then)
            self.visit(node.otherwise)

    def visitApplication(self, node: Application):

        # I am on a possible hole application case
        if not isinstance(node.target, Abstraction):
            if node.argument.type is not None:
                arg_type = node.argument.type
            elif len(self.hole_stack) > 1:
                arg_type = self.hole_stack[-1]
            else:
                arg_type = top
            typee = AbstractionType(self.nextVoidVar(), arg_type,
                                    self.hole_stack[-1])
            self.hole_stack.append(typee)
            self.visit(node.target)
            if typee in self.hole_stack:
                self.hole_stack.remove(typee)
        else:
            self.visit(node.target.body)  # Passar a frente o Abstraction

        oldContext = self.ctx.copy()
        self.ctx = self.ctx.copy()

        tee: Type = top
        if isinstance(node.target, Abstraction):
            if node.target.arg_name.startswith('_'):
                tee = top
            else:
                tee = node.target.arg_type
        elif type(node.target) is Var:
            tee = node.target.type
        elif type(node.target) is Application:
            tee = node.target.type
        elif type(node.target) is TApplication:
            tee = node.target.type
        elif type(node.target) is Hole:
            tee = node.target.type.arg_type
        else:
            tee = node.target.type

        if isinstance(tee, TypeAbstraction):
            tempTee = node.target.type
            while isinstance(tempTee.type, TypeAbstraction):
                tempTee = tempTee.type
            tempTee.type = tempTee.type.return_type if type(
                tempTee.type) is AbstractionType else tempTee.type

        self.hole_stack.append(tee)
        self.visit(node.argument)

        if tee in self.hole_stack:
            self.hole_stack.remove(tee)

        self.ctx = oldContext

        # The type of the argument of the abstraction, is the type of the argument of the application
        if isinstance(node.target,
                      Abstraction) and (node.target.arg_type is None or
                                        node.target.arg_name.startswith('_')):
            # Define the type of the arguments of the abstraction
            node.target.arg_type = node.argument.type

        # The type of the target of current node is the result of the abstraction
        if type(node.target.type) is AbstractionType:
            node.type = node.target.type.return_type
        else:
            node.type = node.target.type

    def visitAbstraction(self, node: Abstraction):

        self.ctx[node.arg_name] = node.arg_type

        # For sure this contains a type
        if node.arg_type is None:
            print(">" * 20, "Opsie, visitAbstraction in hole inferer")

        self.visit(node.body)

        node.type = AbstractionType(node.arg_name, node.arg_type,
                                    node.body.type)

        self.ctx[node.arg_name] = node.arg_type

    def visitDefinition(self, node: Definition):
        # If it native or uninterpreted, skip
        if type(node.body) is Var:
            return None

        # Add the current var to the context
        self.ctx[node.name] = node.type

        oldContext = self.ctx

        bodyNode, typee = self.getBodyAndReturnType(node)

        self.hole_stack = list()

        self.hole_stack.append(typee)
        self.ctx = self.ctx.copy()

        # Visit the body node
        self.visit(bodyNode)

        self.ctx = oldContext
        self.counter = 0

    def visitTAbstraction(self, node: TAbstraction):
        self.visit(node.body)

    def visitTApplication(self, node: TApplication):
        self.visit(node.target)

    def visitTypeAlias(self, node: TypeAlias):
        pass

    def visitTypeDeclaration(self, node: TypeDeclaration):
        pass

    def visitImport(self, node: Import):
        pass

    def visit(self, node):
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
        elif isinstance(node, TypeDeclaration):
            self.visitTypeDeclaration(node)
        elif isinstance(node, TAbstraction):
            self.visitTAbstraction(node)
        elif isinstance(node, TApplication):
            self.visitTApplication(node)
        elif isinstance(node, Import):
            self.visitImport(node)
        else:
            print("Unknown type of node: ", type(node))

    def nextVoidVar(self):
        result = '_infer{}'.format(self.counter)
        self.counter += 1
        return result

    def getBodyAndReturnType(self, node: Definition):

        if not isinstance(node.body, TypeAbstraction):
            return (node.body, node.type)

        current_type: Type = node.type
        current_node: TypedNode = node.body

        # Strip off the TypeAbstractions and TAbstractions
        while isinstance(current_type, TypeAbstraction) and isinstance(
                current_node, TAbstraction):
            typee = current_type.type
            current_node = current_node.body

        # Strip off the function parameters
        while typee != node.return_type and isinstance(
                typee, AbstractionType) and isinstance(current_node,
                                                       Abstraction):
            typee = typee.return_type
            current_node = current_node.body

        return node, typee

    # Given a typee, returns the basic type of it
    def returnBasicTypee(self, typee):
        if isinstance(typee, BasicType):
            return typee
        elif isinstance(typee, RefinedType):
            return self.returnBasicTypee(typee.type)
        elif isinstance(typee, AbstractionType):
            return self.returnBasicTypee(typee.return_type)
        elif isinstance(typee, TypeApplication):
            return self.returnBasicTypee(typee.target)
        elif isinstance(typee, TypeAbstraction):
            return self.returnBasicTypee(typee.type)
