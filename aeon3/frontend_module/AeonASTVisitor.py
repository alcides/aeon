from .generated.AeonParser import AeonParser
from .generated.AeonVisitor import AeonVisitor

from ..ast import *
from ..types import *

class AeonASTVisitor(AeonVisitor):

    def __init__(self, initial_context):
        self.counter = 0
        self.type_aliases = {}

        self.general_context = {}
        self.basic_typee_stack = []

        for x in list(initial_context.keys())[1:]:
            self.general_context[x] = initial_context[x][0].type

    # ------------------------------------------------------------------ Program
    def visitAeon(self, ctx:AeonParser.AeonContext):
        return Program(list(map(self.visit, ctx.children))[:-1])

    # ------------------------------------------------------------------ Imports
    # import path/to/package
    def visitRegularImport(self, ctx:AeonParser.RegularImportContext):
        return Import(self.visit(ctx.path))

    # import function from path/to/package
    def visitSpecialImport(self, ctx:AeonParser.SpecialImportContext):
        return Import(self.visit(ctx.path), ctx.functionName.text)

    def visitImportName(self, ctx:AeonParser.ImportNameContext):
        # If more than one line of import exists, concatenate everything
        if ctx.importName():
            import_name = self.visit(ctx.importName())
            return '{}/{}'.format(ctx.folder.text if ctx.folder else '..', import_name)
        else:
            return ctx.name.text

    # --------------------------------------------------------------- Decl Types
    # type T as T
    def visitTypeeAlias(self, ctx:AeonParser.TypeeAliasContext):
        name = self.visit(ctx.name)
        typee = self.visit(ctx.alias)
        self.type_aliases[name] = typee
        return TypeAlias(name, typee)

    
    def visitTypeeDeclaration(self, ctx:AeonParser.TypeeDeclarationContext):
        typee = self.visit(ctx.name)
        kind = star if type(typee) is BasicType or type(typee) is TypeApplication else typee.kind
        parameters = [self.visit(attribute) for attribute in ctx.typee()[1:]]
        return TypeDeclaration(typee, kind, parameters)
    

    # ----------------------------------------------------------------- Function
    def visitFunction(self, ctx:AeonParser.FunctionContext):

        function_name = ctx.name.text
        return_type = self.visit(ctx.returnType)
        return_name = self.getBasicTypeName(return_type)

        # Update the context
        self.general_context[function_name] = return_type
        oldgeneral_context = self.general_context
        self.general_context = self.general_context.copy()
        
        # Computes de function parameters if they exist
        params, last_param = ctx.params and self.visit(ctx.params) or (None, None)

        if params:
            last_param.return_type = return_type
            typee = params
        else:
            # f() converted into f(_0:Void)
            typee = AbstractionType(Var(self.nextVoidName()), BasicType('Void'), return_type)

        # Compute the where function expression
        conditions = [self.visit(cond) for cond in ctx.expression()]
        distributed_conditions = calculate_where_distribution(conditions)

        # Distributes the And conditions
        for cond, variables in zip(conditions, distributed_conditions):
            if len(variables) > 0:
                typee = apply_distribution(typee, cond, variables)
            else:
                if checkFunctionExistence(cond):
                    name = return_name if type(return_type) is BasicType else return_type.name 
                    apply_distribution(typee, cond, set([name]))
                else:
                    apply_distribution(typee, cond, set())

        # Compute the body if it is not native
        body = self.visit(ctx.body()) if ctx.body() else Var(ctx.native.text)

        # Englobe the body with the function parameters Abstraction
        if function_name != 'main':
            body = Abstraction(typee.arg_name, typee.arg_type, body)
            tempBody = body
            tempTypee = typee.return_type
            while type(tempTypee) is AbstractionType:
                body.body = Abstraction(tempTypee.arg_name, tempTypee.arg_type, body.body)
                body = body.body
                tempTypee = tempTypee.return_type
            body = tempBody
        
        self.counter = 0
        self.general_context = oldgeneral_context

        return Definition(function_name, typee, body)

    # ---------- Function Parameters ----------
    # (x:T, y:U, z:V)
    def visitParameters(self, ctx:AeonParser.ParametersContext):
        typee = self.visit(ctx.param)
        name = self.getBasicTypeName(typee)
        if ctx.restParams:
            rest_params, lastParam = self.visit(ctx.restParams)
            return AbstractionType(name, typee, rest_params), lastParam
        result = AbstractionType(name, typee, None)
        return result, result

    # ------------------------------------------------------------------- Typee
    # ( T )
    def visitTypeeParens(self, ctx:AeonParser.TypeeParensContext):
        return self.visit(ctx.typee())

    # ( T | cond )
    def visitTypeeCondition(self, ctx:AeonParser.TypeeConditionContext):
        typee = self.visit(ctx.typee())
        cond = self.visit(ctx.cond)
        name = self.getBasicTypeName(typee)
        self.basic_typee_stack.append(name.name)
        return RefinedType(name, typee, cond)

    # x:T
    def visitTypeeBasicType(self, ctx:AeonParser.TypeeBasicTypeContext):
        typee = self.visit(ctx.typed) 
        if type(typee) is BasicType:
            if typee in self.type_aliases:
                return self.type_aliases[typee]
        self.basic_typee_stack.append(ctx.varName.text) # TODO: ver se nao eh preciso espaco aqui para previnir
        return typee

    # T -> T
    def visitTypeeAbstraction(self, ctx:AeonParser.TypeeAbstractionContext):
        type1 = self.visit(ctx.type1)
        type2 = self.visit(ctx.type2)
        name = self.getBasicTypeName(type1)
        return AbstractionType(name, type1, type2)
    
    # T<String, Integer> = TypeApplication()
    # TODO: T<X, Y> =
    def visitTypeeAbstractionApplication(self, ctx:AeonParser.TypeeAbstractionApplicationContext):
        result = BasicType(ctx.name.text)
        if ctx.tabst:
            arguments = self.visit(ctx.tabst)
            
            if containsTypeAbst(arguments[-1]):
                result = TypeAbstraction(arguments[-1], Kind(star, star), result)
            else:
                result = TypeApplication(result, arguments[-1])

            for arg in reversed(arguments[:-1]):
                if containsTypeAbst(arg):
                    result = TypeAbstraction(arg, star, result)
                else:
                    result = TypeApplication(result, arg)
        return result

    # ------------------------------------------------------------ Function Body
    # x : T = expression
    def visitBodyVarDefinition(self, ctx:AeonParser.BodyVarDefinitionContext):

        var_type = self.visit(ctx.varType)
        expression = self.visit(ctx.exp)
        var = Var(self.basic_typee_stack.pop() if self.basic_typee_stack else self.nextVoidName())

        if not var_type.name.startswith('_'):
            self.general_context[var_type.name] = var_type

        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), expression)
        else:
            return expression

    # x = expression
    def visitBodyAssignment(self, ctx:AeonParser.BodyAssignmentContext):
        var = Var(ctx.varName.text)
        var_type = self.general_context.get(ctx.varName.text)
        expression = self.visit(ctx.exp)

        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), expression)
        else:
            return expression

    # (\_:Object -> ...) (expression)
    def visitBodyExpression(self, ctx:AeonParser.BodyExpressionContext):
        var = Var(self.nextVoidName())
        expression = self.visit(ctx.expr)
        
        if type(expression) is Var:
            var_type = self.general_context.get(expression.name)
        else:
            var_type = expression.type                
        
        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), expression)
        else:
            return expression

    # if cond {...} else {...}
    def visitIfThenElse(self, ctx:AeonParser.IfThenElseContext):
        var = Var(self.nextVoidName())                                        
        cond = self.visit(ctx.cond)
        then_body = self.visit(ctx.then)
        else_body = self.visit(ctx.elseBody)

        node = If(cond, then_body, else_body)

        if ctx.nextExpr:
            return Application(Abstraction(var, var_type, self.visit(ctx.nextExpr)), node)
        else:
            return node

    # cond ? expr : expr
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
            return Literal(float(value), type=refined_value(float(value), t_f, '_f'))
        elif ctx.value.type == AeonParser.BOOLEAN:
            value = value == 'true' and True or False
            return Literal(value, type=refined_value(value, t_b, '_b'))
        elif ctx.value.type == AeonParser.STRING:
            return Literal(value, type=refined_value(value, t_s, '_s'))             
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
            else: 
                pass # If trying to apply the unary operator to another kind of default value
            return argument

        return Application(operator, argument)

    # f(...)
    def visitFunctionCall(self, ctx:AeonParser.FunctionCallContext):
        functionName = ctx.functionName.text
        params = [Application(Var(functionName), self.visit(parameter)) \
                  for parameter in ctx.expression()]

        # Nest the applications
        for i in range(len(params) - 1, 0, -1):
            params[i].target = params[i - 1]

        if not params:
            result = Application(Var(functionName), empty_argument)
        else:
            result = params[len(params) - 1]

        return result
    
    # \x:T -> expr
    def visitAbstraction(self, ctx:AeonParser.AbstractionContext):
        typee = self.visit(ctx.varType)
        exp = self.visit(ctx.exp)
        name = self.getBasicTypeName(typee)
        return Abstraction(name, typee, exp)

# -------------------------------- HELPERS -------------------------------------
    def nextVoidName(self):
        result = '_{}'.format(self.counter)
        self.counter += 1
        return result

    def getBasicTypeName(self, typee):
        if not self.basic_typee_stack:
            name = Var(self.nextVoidName())
        else:
            name = Var(self.basic_typee_stack.pop())
        return name
        
        

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
    if type(typee) is AbstractionType:
        variables.discard(typee.arg_name.name)
    else:
        variables.discard(typee.name)

    if len(variables) == 0:
        # BasicType is transformed in RefinedType: x:T => {x:T where cond}
        if type(typee) is BasicType:
            return RefinedType(typee.name, typee, cond)
        # Refinement is improved: {T where T.cond} => {T where (T.cond And cond)}
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

# Verifies if the typee contains a "T" type
def containsTypeAbst(typee):
    if type(typee) is BasicType:
        return len(typee.name) == 1
    elif type(typee) is RefinedType:
        return containsTypeAbst(typee.type)
    elif type(typee) is TypeAbstraction:
        return containsTypeAbst(typee.type)
    elif type(typee) is AbstractionType:
        return containsTypeAbst(typee.arg_type) or containsTypeAbst(typee.returnType)
    elif type(typee) is TypeApplication:
        return containsTypeAbst(typee.target) or containsTypeAbst(typee.argument)
    else: # It is of type str
        return len(typee) == 1 


# TODO: Disgrace of implementation to properly discern >(3)(1) refinement from dependent type f(3)
def checkFunctionExistence(cond):

    import aeon3.stdlib

    if type(cond.target) is Application:
        target = checkFunctionExistence(cond.target)
    else:
        target = not aeon3.stdlib.is_builtin(cond.target.name)
    if type(cond.argument) is Application:
        argument = checkFunctionExistence(cond.argument)
    elif type(cond.argument) is Var:
        argument = not aeon3.stdlib.is_builtin(cond.argument.name)
    else:
        argument = False

    return target or argument
