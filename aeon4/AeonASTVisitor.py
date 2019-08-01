from AeonParser import AeonParser
from AeonVisitor import AeonVisitor

from ast import *
from types4 import *
import sys

class AeonASTVisitor(AeonVisitor):
    def __init__(self):
        self.type_aliases = {}
        self.generalContext = {}

    def visitAeon(self, ctx:AeonParser.AeonContext):
        return Program(list(map(self.visit, ctx.children))[:-1])

    def visitRegularImport(self, ctx:AeonParser.RegularImportContext):
        return Import(self.visit(ctx.path))

    def visitSpecialImport(self, ctx:AeonParser.SpecialImportContext):
        return Import(self.visit(ctx.path), self.visit(ctx.functionName))

    def visitImportName(self, ctx:AeonParser.ImportNameContext):
        if ctx.importName():
            result = self.visit(ctx.importName())
        result = self.visitChildren(ctx)
        if result is not None:
            return '{}.{}'.format(ctx.name.text, result)
        return '{}'.format(ctx.name.text)

    def visitTypeeAlias(self, ctx:AeonParser.TypeeAliasContext):
        return TypeAlias(Var(ctx.name.text), self.visit(ctx.typee()))

    '''
    def visitTypeeDeclaration(self, ctx:AeonParser.TypeeDeclarationContext):
        t_abs = ctx.
    '''

    '''
    # Visit a parse tree produced by AeonParser#attribute.
    def visitAttribute(self, ctx:AeonParser.AttributeContext):
        return self.visitChildren(ctx)
    '''

    def visitFunction(self, ctx:AeonParser.FunctionContext):

        if not ctx.params:
            print("TODO:")

        params, lastParam = ctx.params and self.visit(ctx.params) or (None, None)

        returnType = self.visit()
        print('-'*20, params)
        print('-'*20, typee)

        if params:
            lastParam.return_type = typee
            typee = params

        if ctx.body():
            body = self.visit(ctx.body())
        else:
            body = Var(ctx.NATIVE().getText())

        return Definition(ctx.name.text, typee, body)

    def visitSingleParameter(self, ctx:AeonParser.SingleParameterContext):
        if ctx.typee:
            typee = self.visit(ctx.typee())
        else:
            typee = self.visit(ctx.fAbstraction())
        result = AbstractionType(ctx.paramName.text, typee, None)
        # TODO: Nao devolve abstraction type, devolve o tipo da visita de typee adicionando o nome
        return result, result

    def visitMultipleParameters(self, ctx:AeonParser.MultipleParametersContext):
        typee = ctx.typee and self.visit(ctx.typee) or self.visit(ctx.fAbstraction)
        result = self.visit(ctx.parameters)
        return AbstractionType(ctx.paramName.text, typee, result), result




    # TODO: Visit a parse tree produced by AeonParser#typee.
    def visitTypee(self, ctx:AeonParser.TypeeContext):
        return ctx.IDENTIFIER().getText()

    # TODO: Visit a parse tree produced by AeonParser#fAbstraction.
    def visitFAbstraction(self, ctx:AeonParser.FAbstractionContext):
        return self.visitChildren(ctx)







    def visitBodyVarDefinition(self, ctx:AeonParser.BodyVarDefinitionContext):
        var = Var(ctx.varName.getText())
        varType = self.visit(ctx.varType)
        expression = self.visit(ctx.exp)

        self.generalContext[ctx.varName.text] = varType

        if ctx.body:
            return Application(Abstraction(var, varType, self.visit(ctx.body())), expression)
        else:
            return Abstraction(var, varType, expression)

    def visitBodyAssignment(self, ctx:AeonParser.BodyAssignmentContext):
        var = Var(ctx.varName.text)
        varType = ctx[ctx.varName.text]
        expression = self.visit(ctx.exp())
        if ctx.body:
            return Application(Abstraction(var, varType, self.visit(ctx.body())), expression)
        else:
            return Abstraction(var, varType, expression)

    def visitBodyExpression(self, ctx:AeonParser.BodyExpressionContext):
        var = Var('_')
        varType = None                                              # TODO: to be filled after
        expression = self.visit(ctx.expression())
        if ctx.body:
            return Application(Abstraction(var, varType, self.visit(ctx.body())), expression)
        else:
            return Abstraction(var, varType, expression)

    def visitIfThenElse(self, ctx:AeonParser.IfThenElseContext):
        var = Var('_')
        varType = None                                              # TODO: to be filled after

        cond = self.visit(ctx.cond())
        thenBody = self.visit(ctx.then())
        elseBody = self.visit(ctx.elseBody())

        node = If(cond, thenBody, elseBody)

        if ctx.body:
            return Application(Abstraction(var, varType, self.visit(ctx.body())), node)
        else:
            return Abstraction(var, varType, node)

    def visitParenthesis(self, ctx:AeonParser.ParenthesisContext):
        return self.visit(ctx.expression)

    # Visit a parse tree produced by AeonParser#Variable.
    def visitVariable(self, ctx:AeonParser.VariableContext):
        return Var(ctx.IDENTIFIER.getText())


    # Visit a parse tree produced by AeonParser#BinaryOperationCall.
    def visitBinaryOperationCall(self, ctx:AeonParser.BinaryOperationCallContext):
        left = self.visit(ctx.left)
        operation = Var(ctx.op.text)
        right = self.visit(ctx.right)
        return Application(Application(operation, left), right)


    # Visit a parse tree produced by AeonParser#Literal.
    def visitLiteral(self, ctx:AeonParser.LiteralContext):
        if ctx.value.type == AeonParser.INTEGER:
            return int(ctx.INTEGER.getText())
        elif ctx.value.type == AeonParser.FLOAT:
            return float(ctx.FLOAT.getText())
        elif ctx.value.type == AeonParser.BOOLEAN:
            return ctx.BOOLEAN.getText() == 'true' and True or False
        elif ctx.value.type == AeonParser.STRING:
            return ctx.STRING.getText()
        elif ctx.value.type == AeonParser.HOLE:
            return Hole(ctx.HOLE.getText())
        return None


    # Visit a parse tree produced by AeonParser#UnaryOperationCall.
    def visitUnaryOperationCall(self, ctx:AeonParser.UnaryOperationCallContext):
        operator = Var(ctx.op.text)
        argument = self.visit(ctx.right)
        return Application(operator, argument)


    # Visit a parse tree produced by AeonParser#FunctionCall.
    def visitFunctionCall(self, ctx:AeonParser.FunctionCallContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by AeonParser#Abstraction.
    def visitAbstraction(self, ctx:AeonParser.AbstractionContext):
        var = Var(ctx.varName.text)
        typee = self.visit(ctx.varType)
        exp = self.visit(ctx.exp)
        return Abstraction(var, typee, exp)
