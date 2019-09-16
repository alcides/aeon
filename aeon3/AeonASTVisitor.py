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
    # import path.to.package
    def visitRegularImport(self, ctx:AeonParser.RegularImportContext):
        return Import(self.visit(ctx.path))

    # import function from path.to.package
    def visitSpecialImport(self, ctx:AeonParser.SpecialImportContext):
        return Import(self.visit(ctx.path), self.visit(ctx.functionName))

    def visitImportName(self, ctx:AeonParser.ImportNameContext):
        # If more than one line of import exists, concatenate everything
        if ctx.importName():
            return '{}.{}'.format(ctx.name.text, self.visit(ctx.importName()))
        else:
            return '{}'.format(ctx.name.text)

    # ---------------------------------------------------------------- Def Types
    # type T as T
    def visitTypeeAlias(self, ctx:AeonParser.TypeeAliasContext):
        name = self.visit(ctx.name)
        typee = self.visit(ctx.alias)
        self.type_aliases[name] = typee
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

        return_type = self.visit(ctx.returnType)

        # Computes de function parameters if they exist
        params, last_param = ctx.params and self.visit(ctx.params) or (None, None)

        if params:
            last_param.return_type = return_type
            typee = params
        else:
            # f() converted into f(_:Void)
            typee = AbstractionType('_', BasicType('_', 'Void'), return_type)
        
        # Compute the where function expression
        conditions = [self.visit(cond) for cond in ctx.expression()]
        distributed_conditions = calculate_where_distribution(conditions)

        for cond, variables in zip(conditions, distributed_conditions):
            if len(variables) > 0:
                typee = apply_distribution(typee, cond, variables)
            # TODO: Funciona mas nao gosto desta abordagem.... :( 
            else:
                # TODO: perguntar se nao posso por tudo no tipo do output
                if checkFunctionExistence(cond):
                    name = return_type.varName if type(return_type) is BasicType else return_type.name 
                    apply_distribution(typee, cond, set([name]))
                else:
                    apply_distribution(typee, cond, set())

        # Compute the body if it is not native
        if ctx.body():
            body = self.visit(ctx.body())
        else:
            body = Var(ctx.native.text)

        return Definition(self.visit(ctx.name), typee, body)

    # ---------- Function Parameters ----------
    # (x:T, y:U, z:V)
    def visitParameters(self, ctx:AeonParser.ParametersContext):
        typee = self.visit(ctx.param)
        if ctx.restParams:
            restParams, lastParam = self.visit(ctx.restParams)
            return AbstractionType(typee.name, typee, restParams), lastParam
        result = AbstractionType(typee.name, typee, None)
        return result, result

    # ------------------------------------------------------------------- Typee
    # ( T )
    def visitTypeeParenthesis(self, ctx:AeonParser.TypeeParenthesisContext):
        return self.visitChildren(ctx)

    # ( T where cond )
    def visitTypeeCondition(self, ctx:AeonParser.TypeeConditionContext):
        typee = self.visit(ctx.typee())
        cond = self.visit(ctx.cond)
        return RefinedType(typee.name, typee, cond)

    # T
    def visitTypeeBasicType(self, ctx:AeonParser.TypeeBasicTypeContext):
        typeeName = self.visit(ctx.basicType) 
        if typeeName in self.type_aliases:
            return self.type_aliases[typeeName]
        if isinstance(typeeName, str):
            return BasicType(ctx.typeName.text, typeeName)
        return typeeName
    # T -> T
    def visitTypeeAbstraction(self, ctx:AeonParser.TypeeAbstractionContext):
        # TODO: review: deve de estar errado
        return AbstractionType('_', self.visit(ctx.type1), self.visit(ctx.type2))
    
    # Visit a parse tree produced by AeonParser#TypeeUnnamedType.
    def visitTypeeUnnamedType(self, ctx:AeonParser.TypeeUnnamedTypeContext):
        typeeName = self.visit(ctx.basicType)
        if typeeName in self.type_aliases:
            return self.type_aliases[typeeName]
        return BasicType('_', typeeName)
    
    # Visit a parse tree produced by AeonParser#typedName.
    # TODO: Has to return a typee
    def visitTypedName(self, ctx:AeonParser.TypedNameContext):
        result = ctx.name.text
        if ctx.tabst:
            result = '{}<{}>'.format(result, self.visit(ctx.tabst))
        return result

    # ------------------------------------------------------------ Function Body
    # x : T = expression
    def visitBodyVarDefinition(self, ctx:AeonParser.BodyVarDefinitionContext):

        var_type = self.visit(ctx.varType)
        expression = self.visit(ctx.exp)
        var = Var(var_type.name)

        if var_type.name is not '_':
            self.generalContext[var_type.name] = var_type

        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), expression)
        else:
            return Abstraction(var, var_type, expression)

    # x = expression
    def visitBodyAssignment(self, ctx:AeonParser.BodyAssignmentContext):
        var = Var(ctx.varName.text)
        var_type = self.generalContext.get(ctx.varName.text)   # None if undeclared variable
        expression = self.visit(ctx.exp)

        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), expression)
        else:
            return Abstraction(var, var_type, expression)

    # (\_:Object -> ...) (expression)
    def visitBodyExpression(self, ctx:AeonParser.BodyExpressionContext):
        var = Var('_')
        expression = self.visit(ctx.expr)
        
        if type(expression) is Var:
            var_type = self.generalContext.get(expression.name)
        else:
            var_type = expression.type                  # TODO: to be filled after
        
        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), expression)
        else:
            return Abstraction(var, var_type, expression)

    # if cond {...} else {...}
    def visitIfThenElse(self, ctx:AeonParser.IfThenElseContext):
        var = Var('_')
        var_type = None                                                         
        cond = self.visit(ctx.cond)
        then_body = self.visit(ctx.then)
        else_body = self.visit(ctx.elseBody)

        node = If(cond, then_body, else_body)

        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), node)
        else:
            return Abstraction(var, var_type, node)

    # if cond then expr else expr
    def visitIfThenElseExpr(self, ctx:AeonParser.IfThenElseExprContext):
        cond = self.visit(ctx.cond)
        then_body = self.visit(ctx.then)
        else_body = self.visit(ctx.elseBody)
        return If(cond, then_body, else_body)

    # ( expr )
    def visitParenthesis(self, ctx:AeonParser.ParenthesisContext):
        return self.visit(ctx.expression())

    # x
    def visitVariable(self, ctx:AeonParser.VariableContext):
        return Var(ctx.varName.text)

    # x operator y
    def visitBinaryOperationCall(self, ctx:AeonParser.BinaryOperationCallContext):
        left = self.visit(ctx.left)
        operation = Var(ctx.op.text)
        right = self.visit(ctx.right)
        return Application(Application(operation, left), right)

    # 0, 1, true, false, "string", hole
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
            return Hole(value)                                                          
        return None

    # not/- expr
    def visitUnaryOperationCall(self, ctx:AeonParser.UnaryOperationCallContext):

        operator = Var(ctx.op.text)
        argument = self.visit(ctx.right)

        if type(argument) is Literal:
            if argument.type.type is t_b:
                argument.value = not argument.value
                argument.type.cond.argument.value = not argument.type.cond.argument.value
            elif argument.type.type is t_i:
                argument.value = -argument.value
                argument.type.cond.argument.value = -argument.type.cond.argument.value
            else: # If trying to apply the unary operator to another kind of default value
                pass
            return argument

        return Application(operator, argument)

    # f(...)
    def visitFunctionCall(self, ctx:AeonParser.FunctionCallContext):
        functionName = self.visit(ctx.functionName)
        params = [Application(Var(functionName), self.visit(parameter)) \
                  for parameter in ctx.expression()]

        # Nest the applications
        for i in range(len(params) - 1, 0, -1):
            params[i].target = params[i - 1]

        if not params:
            # TODO: calling a function with no arguments. Application or Var?
            # result = Var(ctx.functionName.text)
            result = Application(Var(functionName), None)
        else:
            result = params[len(params) - 1]

        return result
    
    # \x:T -> expr
    def visitAbstraction(self, ctx:AeonParser.AbstractionContext):
        typee = self.visit(ctx.varType)
        exp = self.visit(ctx.exp)
        return Abstraction(Var(typee.name), typee, exp)

    # Class.function
    def visitDottedName(self, ctx:AeonParser.DottedNameContext):
        result = self.visit(ctx.name)
        if ctx.dotted:
            result = '{}.{}'.format(result, ctx.dotted.text)
        return result

    # Visit a parse tree produced by AeonParser#abstrParams.
    def visitAbstrParams(self, ctx:AeonParser.AbstrParamsContext):

        result = ctx.param.text

        if ctx.restParams:
            result = '{},{}'.format(result, self.visit(ctx.restParams))

        return result

# -------------------------------- HELPERS -------------------------------------
def refined_value(v, t, label="_v"):
    app1 = Application(Var(t == t_b and "===" or "=="), Var(label))
    app2 = Application(app1, Literal(v, type=t))
    return RefinedType(label, t, app2)

def calculate_where_distribution(conditions):
    result = [] 
    def recursive_print(cond, variables):
        if type(cond.target) is Application:
            recursive_print(cond.target, variables)
        if type(cond.argument) is Application:
            recursive_print(cond.argument, variables)
        elif type(cond.argument) is Var:
            variables.add(cond.argument.name)

    for cond in conditions:
        variables = set()
        recursive_print(cond, variables)
        result.append(variables)

    return result

def apply_distribution(typee, cond, variables):
    
    # Try to remove the variable name of the current type
    variables.discard(typee.name)

    if len(variables) == 0:
        # BasicType is transformed in RefinedType: T => {T where cond}
        if type(typee) is BasicType:
            return RefinedType(typee.name, typee, cond)
        # Refinement is improved: {T where T.cond} => {T where (T.cond && cond)}
        elif type(typee) is RefinedType:
            typee.cond = Application(Application(Var('And'), typee.cond), cond)
            return typee
        # Improve the BasicType or RefinedType within the AbstractionType.
        elif type(typee) is AbstractionType:
            typee.arg_type = apply_distribution(typee.arg_type, cond, variables)
            return typee
    
    # Control undefined variables
    if type(typee) is not AbstractionType:
        return apply_distribution(typee, cond, set())
    else:
        typee.return_type = apply_distribution(typee.return_type, cond, variables)
        return typee






# TODO: Disgrace of implementation to properly discern 3 > 1 refinement from dependent type f(3)
def checkFunctionExistence(cond):
    if type(cond.target) is Application:
        target = checkFunctionExistence(cond.target)
    else:
        if cond.target.name not in ['+', '-', '*', '/', '%', '^', '&&', '||', '!', '<', \
                         '<=', '>', '>=', '==', '!=', '===', '!==']:
            target = True
        else:
            target = False
    if type(cond.argument) is Application:
        argument = checkFunctionExistence(cond.argument)
    elif type(cond.argument) is Var:
        if cond.argument.name not in ['+', '-', '*', '/', '%', '^', '&&', '||', '!', '<', \
                         '<=', '>', '>=', '==', '!=', '===', '!==']:
            argument = True
        else:
            argument = False
    else:
        argument = False

    return target or argument






def resolve_imports():
    # TODO:
    pass