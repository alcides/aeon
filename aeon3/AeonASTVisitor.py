from AeonParser import AeonParser
from AeonVisitor import AeonVisitor

from ast import *
from types4 import *
import sys

class AeonASTVisitor(AeonVisitor):
    def __init__(self):
        self.type_aliases = {}
        self.generalContext = {}

    # ------------------------------------------------------------------ Program
    def visitAeon(self, ctx:AeonParser.AeonContext):
        return Program(list(map(self.visit, ctx.children))[:-1])

    # ------------------------------------------------------------------ Imports
    def visitRegularImport(self, ctx:AeonParser.RegularImportContext):
        return Import(self.visit(ctx.path))

    def visitSpecialImport(self, ctx:AeonParser.SpecialImportContext):
        return Import(self.visit(ctx.path), ctx.functionName.text)

    def visitImportName(self, ctx:AeonParser.ImportNameContext):
        if ctx.importName():
            result = self.visit(ctx.importName())
        result = self.visitChildren(ctx)
        if result is not None:
            return '{}.{}'.format(ctx.name.text, result)
        return '{}'.format(ctx.name.text)

    # ---------------------------------------------------------------- Def Types
    def visitTypeeAlias(self, ctx:AeonParser.TypeeAliasContext):
        name = ctx.name.text
        typee = self.visit(ctx.typee())
        self.generalContext[name] = typee
        return TypeAlias(name, typee)

    '''
    def visitTypeeDeclaration(self, ctx:AeonParser.TypeeDeclarationContext):
        t_abs = ctx.
    '''

    '''
    # Visit a parse tree produced by AeonParser#attribute.
    def visitAttribute(self, ctx:AeonParser.AttributeContext):
        return self.visitChildren(ctx)
    '''

    # ----------------------------------------------------------------- Function
    def visitFunction(self, ctx:AeonParser.FunctionContext):

        returnName = ctx.returnName.text
        returnType = self.visit(ctx.returnType)

        # All types excluding BasicType require a name
        if type(returnType) is not BasicType:
            returnType.name = returnName

        params, lastParam = ctx.params and self.visit(ctx.params) or (None, None)

        if params:
            lastParam.return_type = returnType
            typee = params
        else:
            typee = returnType

        if ctx.body():
            body = self.visit(ctx.body())
        else:
            body = Var(ctx.native.text)

        return Definition(ctx.name.text, typee, body)

    # ---------- Parameters ----------
    def visitSingleParameter(self, ctx:AeonParser.SingleParameterContext):
        typee = self.visit(ctx.typee())
        typee.name = type(typee) is not BasicType and ctx.paramName.text or typee.name
        result = AbstractionType(ctx.paramName.text, typee, None)
        return result, result

    def visitMultipleParameters(self, ctx:AeonParser.MultipleParametersContext):
        params, lastParam = self.visit(ctx.parameters())
        typee = self.visit(ctx.typee())
        typee.name = type(typee) is not BasicType and ctx.paramName.text or typee.name
        return AbstractionType(ctx.paramName.text, typee, params), lastParam

    # ---------- Typee ----------
    def visitTypeeParenthesis(self, ctx:AeonParser.TypeeParenthesisContext):
        return self.visitChildren(ctx)

    def visitTypeeCondition(self, ctx:AeonParser.TypeeConditionContext):
        name = None
        typee = self.visit(ctx.typee())
        cond = self.visit(ctx.cond)
        return RefinedType(name, typee, cond)

    def visitTypeeBasicType(self, ctx:AeonParser.TypeeBasicTypeContext):
        return BasicType(ctx.basicType.text);

    # TODO: Visit a parse tree produced by AeonParser#fAbstraction.
    def visitFAbstraction(self, ctx:AeonParser.FAbstractionContext):
        return self.visitChildren(ctx)






    # ------------------------------------------------------------ Function Body
    def visitBodyVarDefinition(self, ctx:AeonParser.BodyVarDefinitionContext):
        var = Var(ctx.varName.text)
        varType = self.visit(ctx.varType)
        expression = self.visit(ctx.exp)

        self.generalContext[ctx.varName.text] = varType

        if ctx.body():
            return Application(Abstraction(var, varType, self.visit(ctx.body())), expression)
        else:
            return Abstraction(var, varType, expression)

    def visitBodyAssignment(self, ctx:AeonParser.BodyAssignmentContext):
        var = Var(ctx.varName.text)
        varType = ctx.get(ctx.varName.text)
        expression = self.visit(ctx.exp())
        if ctx.body():
            return Application(Abstraction(var, varType, self.visit(ctx.body())), expression)
        else:
            return Abstraction(var, varType, expression)

    def visitBodyExpression(self, ctx:AeonParser.BodyExpressionContext):
        var = Var('_')
        expression = self.visit(ctx.expression())
        if type(expression) is Var:
            varType = self.generalContext.get(expression.name)
        else:
            varType = expression.type                                          # TODO: to be filled after
        if ctx.body():
            return Application(Abstraction(var, varType, self.visit(ctx.body())), expression)
        else:
            return Abstraction(var, varType, expression)

    def visitIfThenElse(self, ctx:AeonParser.IfThenElseContext):
        var = Var('_')
        varType = None                                              # TODO: to be filled after

        cond = self.visit(ctx.cond)
        thenBody = self.visit(ctx.then)
        elseBody = self.visit(ctx.elseBody)

        node = If(cond, thenBody, elseBody)

        if ctx.body():
            return Application(Abstraction(var, varType, self.visit(ctx.body())), node)
        else:
            return Abstraction(var, varType, node)

    # Visit a parse tree produced by AeonParser#IfThenElseExpr.
    def visitIfThenElseExpr(self, ctx:AeonParser.IfThenElseExprContext):
        var = Var('_')
        varType = None                                              # TODO: to be filled after

        cond = self.visit(ctx.cond)
        thenBody = self.visit(ctx.then)
        elseBody = self.visit(ctx.elseBody)

        return If(cond, thenBody, elseBody)

    def visitParenthesis(self, ctx:AeonParser.ParenthesisContext):
        return self.visit(ctx.expression())

    def visitVariable(self, ctx:AeonParser.VariableContext):
        return Var(ctx.varName.text)

    def visitBinaryOperationCall(self, ctx:AeonParser.BinaryOperationCallContext):
        left = self.visit(ctx.left)
        operation = Var(ctx.op.text)
        right = self.visit(ctx.right)
        return Application(Application(operation, left), right)

    def visitLiteral(self, ctx:AeonParser.LiteralContext):
        value = ctx.value.text
        if ctx.value.type == AeonParser.INTEGER:
            return Literal(int(value), type=refined_value(int(value), t_i, '_i'))
        elif ctx.value.type == AeonParser.FLOAT:
            return Literal(float(value), type=refined_value(float(value), t_f, '_f'))   # TODO: improve refinement
        elif ctx.value.type == AeonParser.BOOLEAN:
            value = value == 'true' and True or False
            return Literal(value, type=refined_value(value, t_b, '_b'))
        elif ctx.value.type == AeonParser.STRING:
            return Literal(value, type=refined_value(value, t_s, '_s'))                 # TODO: improve the refinement
        elif ctx.value.type == AeonParser.HOLE:
            return Hole(value)                                                          # TODO: Beware the Hole
        return None


    # Visit a parse tree produced by AeonParser#UnaryOperationCall.
    def visitUnaryOperationCall(self, ctx:AeonParser.UnaryOperationCallContext):
        operator = Var(ctx.op.text)
        argument = self.visit(ctx.right)

        if type(argument) is Literal:
            argument.value = argument.type.type is t_b and not argument.value or -argument.value
            return argument

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

# -------------------------------- HELPERS -------------------------------------
def refined_value(v, t, label="_v"):
    app1 = Application(Var(t == t_b and "===" or "=="), Var(label))
    app2 = Application(app1, Literal(v, type=t))
    return RefinedType(label, t, app2)
