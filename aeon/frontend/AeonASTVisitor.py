from typing import List

from .generated.AeonParser import AeonParser
from .generated.AeonVisitor import AeonVisitor

from aeon.ast import Var, Literal, Definition, TypeAlias, TypeDeclaration, Program, Import, Abstraction, Application, If, Hole, TAbstraction, TApplication
from aeon.types import Type, BasicType, AbstractionType, RefinedType, TypeApplication, TypeAbstraction, Kind, star, bottom, t_v, t_i, t_f, t_b, t_s, top, t_delegate

from functools import reduce


class AeonASTVisitor(AeonVisitor):
    def __init__(self, context):
        self.counter = 0
        self.type_aliases = {}

        self.declarations = []
        self.general_context = {}
        self.basic_typee_stack = []

        for x in list(context.keys()):
            curr = context[x][0]
            if isinstance(curr, TypeAlias):
                self.type_aliases[curr.name] = curr
            elif isinstance(curr, TypeDeclaration):
                self.general_context[x] = curr
            else:
                self.general_context[x] = curr

    # -------------------------------------------------------------------------
    # ----------------------------------------------------------------- Program
    def visitAeon(self, ctx: AeonParser.AeonContext):
        for child in ctx.children:
            self.counter = 0
            self.basic_typee_stack = []
            child = self.visit(child)
            if child is not None:
                self.declarations.append(child)
        return Program(self.declarations)

    # -------------------------------------------------------------------------
    # ----------------------------------------------------------------- Imports
    def visitImprt(self, ctx: AeonParser.ImprtContext):
        return self.visitChildren(ctx)

    # import path/to/package
    def visitRegular_import(self, ctx: AeonParser.Regular_importContext):
        return Import(self.visit(ctx.path))

    # import function from path/to/package
    def visitFunction_import(self, ctx: AeonParser.Function_importContext):
        return Import(self.visit(ctx.path), ctx.functionName.text)

    # 'path/../to/../package'
    def visitImport_path(self, ctx: AeonParser.Import_pathContext):
        return str(
            reduce(lambda path, package: '{}{}'.format(path, package),
                   ctx.children))

    # -------------------------------------------------------------------------
    # --------------------------------------------------------------- TypeAlias
    # type T as U
    def visitTypee_alias(self, ctx: AeonParser.Typee_aliasContext):
        name = self.visit(ctx.name)
        alias = self.visit(ctx.alias)
        self.type_aliases[name] = alias
        return TypeAlias(name, alias)

    # -------------------------------------------------------------------------
    # --------------------------------------------------------- TypeDeclaration
    def visitTypee_declaration(self, ctx: AeonParser.Typee_declarationContext):
        return self.visitChildren(ctx)

    # type Person
    def visitRegular_typee_declaration(
            self, ctx: AeonParser.Regular_typee_declarationContext):
        return TypeDeclaration(self.visit(ctx.name), star)

    # type Person<T> { ... }
    def visitParameterized_typee_declaration(
            self, ctx: AeonParser.Parameterized_typee_declarationContext):

        typee = self.visit(ctx.name)
        typee_name = self.returnBasicTypee(typee).name

        parameters = self.visit(ctx.params)
        names = [self.getBasicTypeName(param) for param in parameters]

        # Guardar a declaracao do tipo
        self.declarations.append(
            TypeDeclaration(typee, self.getTypeeKind(typee)))

        # Create the uninterpreted functions
        for name, param in zip(names, parameters):
            function_name = '_{}_{}'.format(typee_name, name)
            function_type = AbstractionType('_', typee, param)
            definition = Definition(function_name, function_type, param,
                                    Var('uninterpreted').with_type(bottom))
            self.declarations.append(definition)
            self.general_context[function_name] = function_type

        # On purpose to prevent function declarations before type declaration
        return None

    # [size:Int, weight:Double, name:String]
    def visitParameters_typee_declaration(
            self, ctx: AeonParser.Parameters_typee_declarationContext):
        return [self.visit(typee) for typee in ctx.typee_definition()]

    # -------------------------------------------------------------------------
    # ------------------------------------------------------------------- Typee
    def visitTypee(self, ctx: AeonParser.TypeeContext):
        return self.visitChildren(ctx)

    # {T | condition}
    def visitTypee_refined(self, ctx: AeonParser.Typee_refinedContext):
        typee = self.visit(ctx.typeeRefined)
        name = self.getBasicTypeName(typee)
        condition = self.visit(ctx.condition)
        return RefinedType(name, typee, condition)

    # (T -> U)
    def visitTypee_abstraction_type(
            self, ctx: AeonParser.Typee_abstraction_typeContext):
        argTypee = self.visit(ctx.argTypee)
        name = self.getBasicTypeName(argTypee)
        returnTypee = self.visit(ctx.returnTypee)
        return AbstractionType(name, argTypee, returnTypee)

    # x : T
    def visitTypee_definition(self, ctx: AeonParser.Typee_definitionContext):
        self.basic_typee_stack.append(ctx.varName.text)
        typee = self.visit(ctx.varTypee)
        self.general_context[ctx.varName.text] = typee
        return typee

    # T, V, Integer, String, Boolean
    def visitTypee_basic_type(self, ctx: AeonParser.Typee_basic_typeContext):
        typee = BasicType(ctx.basicType.text)
        #if typee in self.type_aliases:
        #return self.type_aliases[typee]
        return typee

    # Map<K, V> : (* => *) => *
    def visitTypee_type_abstract(self,
                                 ctx: AeonParser.Typee_type_abstractContext):
        typee: Type = BasicType(ctx.abstractType.text)
        abstractions, applications = self.visit(ctx.abstractParams)
        # Englobe the typee in the applications and abstractions
        typee = reduce(
            lambda target, argument: TypeApplication(target, argument),
            applications, typee)
        typee = reduce(
            lambda abst, retType: TypeAbstraction(retType, star, abst),
            abstractions, typee)
        return typee

    # ([X, Y, Z], [T1, T2, ..., Tn])
    def visitTypee_abstract_parameters(
            self, ctx: AeonParser.Typee_abstract_parametersContext):
        abstractions: List[Type] = []
        applications = []

        for typee in ctx.typee():
            typee = self.visit(typee)
            abstractions += self.searchAbstractions(typee)
            typee = self.treatTypee(typee)
            applications.append(typee)

        # In order to remove duplicates from the list and keep the order
        return (list(dict.fromkeys(reversed(abstractions))), applications)

    # Search for abstractions in a given T and return the list of them: [X, Y, Z]
    def searchAbstractions(self, typee):
        abstractions = []
        # Check if the BasicType is a TypeeIdentifier
        if isinstance(typee, BasicType):
            if len(typee.name) == 1:
                abstractions = [typee.name]
        # Check the RefinedType type
        elif isinstance(typee, RefinedType):
            abstractions = self.searchAbstractions(typee.type)
        # Check the AbstractionType arg_type and return_type
        elif isinstance(typee, AbstractionType):
            arg_type = self.searchAbstractions(typee.arg_type)
            return_type = self.searchAbstractions(typee.return_type)
            abstractions = arg_type + return_type
        # Check the TypeApplication target and argument
        elif isinstance(typee, TypeApplication):
            target = self.searchAbstractions(typee.target)
            argument = self.searchAbstractions(typee.argument)
            abstractions = target + argument
        # Check the name of each TypeAbstraction, progress the typee and return it
        elif isinstance(typee, TypeAbstraction):
            while isinstance(typee, TypeAbstraction):
                abstractions = abstractions + self.searchAbstractions(
                    typee.name)
                typee = typee.type
            abstractions = abstractions + self.searchAbstractions(typee)
        return abstractions

    # Removes every single TypeAbstraction and returns the type
    def treatTypee(self, typee):
        if isinstance(typee, BasicType):
            return typee
        elif isinstance(typee, RefinedType):
            typee.type = self.treatTypee(typee.type)
        elif isinstance(typee, AbstractionType):
            typee.arg_type = self.treatTypee(typee.arg_type)
            typee.return_type = self.treatTypee(typee.return_type)
        elif isinstance(typee, TypeApplication):
            typee.target = self.treatTypee(typee.target)
            typee.argument = self.treatTypee(typee.argument)
        elif isinstance(typee, TypeAbstraction):
            typee = self.treatTypee(typee.type)
        return typee

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

    # Discover typee kind. Given a typee, discovers its kind
    def getTypeeKind(self, typee):
        if isinstance(typee, BasicType):
            return star
        elif isinstance(typee, RefinedType):
            return star
        elif isinstance(typee, AbstractionType):
            return star
        elif isinstance(typee, TypeApplication):
            return Kind(self.getTypeeKind(typee.target), star)
        elif isinstance(typee, TypeAbstraction):
            return Kind(self.getTypeeKind(typee.type), star)

    # -------------------------------------------------------------------------
    # ---------------------------------------------------------------- Function
    # Visit a parse tree produced by AeonParser#function.
    def visitFunction(self, ctx: AeonParser.FunctionContext):

        name, (abstractions, _) = self.visit(ctx.name)

        self.general_context[name] = None

        # Update the general context
        old_context = self.general_context.copy()
        self.general_context = self.general_context.copy()

        # Get the parameters and set the return type
        if ctx.params:
            typee, lastTypee = self.visit(ctx.params)
            return_type = self.visit(ctx.returnType)
            lastTypee.return_type = return_type
        else:
            return_type = self.visit(ctx.returnType)
            typee = AbstractionType('_', t_v, return_type)

        # Re-distribute the where statements
        if ctx.where:
            return_name = self.getBasicTypeName(return_type)
            conditions = self.visit(ctx.where)
            return_type = self.distribute_where_expressions(
                typee, return_name, return_type, conditions)

        # >>>>>> TODO: falta envolver nas tapplications
        # TODO: (alcides) alterei o kind para star, mas devia ser calculado
        for type_abstract in abstractions:
            typee = TypeAbstraction(type_abstract, star, typee)

        # The typee is fully completed
        self.general_context[name] = typee

        # Visit the body
        body = self.visit(ctx.body)

        # Only englobe if it is not main nor native
        if name is 'main':
            body = Abstraction('_', t_v, body)
        elif (not isinstance(body, Var)
              or (isinstance(body, Var) and body.name != 'native')):

            # If there are parameters, englobe the body in them
            tempTypee = typee

            while isinstance(tempTypee, TypeAbstraction):
                tempTypee = tempTypee.type
            listParams = []

            while tempTypee != return_type:
                listParams.append((tempTypee.arg_name, tempTypee.arg_type))
                tempTypee = tempTypee.return_type
            listParams.reverse()

            for param_name, param_typee in listParams:
                body = Abstraction(param_name, param_typee, body)
                body.type = AbstractionType(param_name, param_typee,
                                            body.body.type)

            # If there are abstractions, englobe the body and typee in them
            for type_abstract in abstractions:
                body = TAbstraction(type_abstract, star, body)
                body.type = TypeAbstraction(type_abstract, star,
                                            body.body.type)

        # Re-update the context
        self.general_context = old_context
        self.general_context[name] = typee

        self.counter = 0
        self.basic_typee_stack = []

        return Definition(name, typee, body, return_type)

    # f<T, Integer>
    def visitFunction_identifier(self,
                                 ctx: AeonParser.Function_identifierContext):
        name = ctx.name.text
        abstractions, applications = self.visit(
            ctx.abstractParams) if ctx.abstractParams else ([], [])
        return name, (abstractions, applications)

    # (x:Integer, y:T, z:Map<Double, String>)
    def visitFunction_parameters(self,
                                 ctx: AeonParser.Function_parametersContext):
        parameters = []
        for param in ctx.typee():
            typee = self.visit(param)
            name = self.getBasicTypeName(typee)
            parameters.append((name, typee))
        parameters.reverse()
        firstParam = AbstractionType(parameters[0][0], parameters[0][1], None)
        lastParam = firstParam
        for name, param in parameters[1:]:
            firstParam = AbstractionType(name, param, firstParam)
        return firstParam, lastParam

    # ... where {x == 0 and 1 > 0}
    def visitFunction_where(self, ctx: AeonParser.Function_whereContext):
        return [self.visit(expression) for expression in ctx.expression()]

    # ----------------------------------------------------------- Function Body
    # function : () -> T = native
    def visitNativeBody(self, ctx: AeonParser.NativeBodyContext):
        return Var(ctx.native.text)

    def visitUninterpretedBody(self, ctx: AeonParser.UninterpretedBodyContext):
        return Var(ctx.uninterpreted.text)

    # function : () -> T { ... }
    def visitRegularBody(self, ctx: AeonParser.RegularBodyContext):
        statements = [self.visit(statement) for statement in ctx.statement()]
        statements.reverse()
        node = statements[0]

        # Prevent definitions at the end of the function
        node = node.body if isinstance(node, Definition) else node

        for statement in statements[1:]:
            if isinstance(statement, Definition):
                name, typee, body = statement.name, statement.type, statement.body
            else:
                name, typee, body = '_', top, statement

            # Create the abstraction and application
            node = Application(Abstraction(name, typee, node), body)
        return node

    # -------------------------------------------------------------------------
    # -------------------------------------------------------------- Statements
    def visitStatement(self, ctx: AeonParser.StatementContext):
        return self.visitChildren(ctx)

    # x : T = expression
    def visitVariable_definition(self,
                                 ctx: AeonParser.Variable_definitionContext):
        typee = self.visit(ctx.variable)
        variable = self.getBasicTypeName(typee)
        expression = self.visit(ctx.exp)

        self.general_context[variable] = typee

        return Definition(variable, typee, expression, typee)

    # x = expression
    def visitVariable_assignment(self,
                                 ctx: AeonParser.Variable_assignmentContext):
        typee = self.general_context.get(ctx.variable.text)
        variable = Var(ctx.variable.text).with_type(typee)
        expression = self.visit(ctx.exp)

        if variable.name not in self.general_context:
            typee = expression.type
            self.general_context[variable.name] = typee

        return Definition(variable, typee, expression, typee)

    # if condition { ... } else { ... }
    def visitIf_statement(self, ctx: AeonParser.If_statementContext):
        condition = self.visit(ctx.cond)
        then = self.visit(ctx.then)
        otherwise = self.visit(ctx.otherwise)
        typee = self.leastUpperBound(then.type, otherwise.type)
        return If(condition, then, otherwise)

    # -------------------------------------------------------------------------
    # ------------------------------------------------------------. Expressions
    # ( expression )
    def visitParenthesis(self, ctx: AeonParser.ParenthesisContext):
        return self.visit(ctx.expression())

    # [ T ]
    def visitHole(self, ctx: AeonParser.HoleContext):
        typee = self.visit(ctx.typee()) if ctx.typee() else None
        return Hole(typee)

    # x
    def visitVariable(self, ctx: AeonParser.VariableContext):
        return Var(ctx.variable.text)

    # 1, 1.0, "Hello World", true, false
    def visitLiteral(self, ctx: AeonParser.LiteralContext):
        value = ctx.value.text
        if ctx.value.type == AeonParser.INTEGER:
            return Literal(int(value),
                           type=self.refined_value(int(value), t_i, '_i'))
        elif ctx.value.type == AeonParser.FLOAT:
            return Literal(float(value),
                           type=self.refined_value(float(value), t_f, '_f'))
        elif ctx.value.type == AeonParser.BOOLEAN:
            value = value == 'true' and True or False
            return Literal(value, type=self.refined_value(value, t_b, '_b'))
        elif ctx.value.type == AeonParser.STRING:
            return Literal(value, type=self.refined_value(value, t_s, '_s'))
        return None

    # x -> y, x == y, x || y, x && y, x > y, x < y, ...
    def visitLogicalExpression(self, ctx: AeonParser.LogicalExpressionContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        operator = Var(ctx.op.text)

        if operator.name not in ['||', '&&']:
            operator = TApplication(operator, t_delegate)

        return Application(Application(operator, left), right)

    # x + y, x - y, x * y, x ^ y, ...
    def visitNumberExpression(self, ctx: AeonParser.NumberExpressionContext):
        left = self.visit(ctx.left)
        right = self.visit(ctx.right)
        operator = TApplication(Var(ctx.op.text), t_delegate)
        return Application(Application(operator, left), right)

    # !expression or -expression
    def visitUnaryOperation(self, ctx: AeonParser.UnaryOperationContext):

        expression = self.visit(ctx.right)
        operator = Var(ctx.op.text)

        # It is -expression
        if ctx.op.type is AeonParser.MINUS:
            left = Literal(0, type=self.refined_value(int(0), t_i, '_i'))
            operator = TApplication(operator, t_delegate)
            expression = Application(Application(operator, left), expression)

        # It is !expression
        else:
            if isinstance(expression, Literal):
                expression.value = not expression.value
                expression.type.cond.argument.value = not expression.type.cond.argument.value
            else:
                expression = Application(operation, expression)
        return expression

    # cond ? then : otherwise
    def visitIfExpression(self, ctx: AeonParser.IfExpressionContext):
        condition = self.visit(ctx.cond)
        then = self.visit(ctx.then)
        otherwise = self.visit(ctx.otherwise)
        return If(condition, then, otherwise)

    # variavel.atributo
    # TODO: small complication with tabstractions and tapplications
    def visitTypeeAttributeCall(self,
                                ctx: AeonParser.TypeeAttributeCallContext):
        variable = ctx.variable.text
        attribute = ctx.attribute.text

        arg_typee = self.general_context[variable]
        target_name = '_{}_{}'.format(
            self.returnBasicTypee(arg_typee).name, attribute)

        target = Var(target_name)
        argument = Var(variable)

        return Application(target, argument)

    # \\x:T -> expression
    def visitAbstractionExpression(
            self, ctx: AeonParser.AbstractionExpressionContext):
        typee = self.visit(ctx.variable)
        name = self.getBasicTypeName(typee)
        expression = self.visit(ctx.exp)

        abstraction_typee = AbstractionType(name, typee, expression.type)
        abstraction = Abstraction(name, typee, expression)

        listAbstractions = list(
            dict.fromkeys(reversed(self.searchAbstractions(typee))))

        for abstr in listAbstractions:
            abstraction = TAbstraction(abstr, star, abstraction)
            abstraction.type = TypeAbstraction(abstr, star,
                                               abstraction.body.type)

        return abstraction

    # expression <Integer, Boolean>? ( ... )
    def visitFunctionCall(self, ctx: AeonParser.FunctionCallContext):
        expression = self.visit(ctx.target)
        applications = self.visit(ctx.app) if ctx.app else []
        parameters = self.visit(ctx.params) if ctx.params else [Var('_')]

        for application in applications:
            expression = TApplication(expression, application)
            #expression.type = TypeApplication(expression.target.type,
            #                                  application)

        for param in parameters:
            expression = Application(expression, param)
            expression.type = self.getReturnType(
                expression.type)  # TODO: isto nao esta bem
            # TODO: isto nao esta bem?? Confirmar, parece-me bem

        return expression

    # @maximize(...), @minimze(...) and @evaluate(...)
    def visitFitnessImprovement(self,
                                ctx: AeonParser.FitnessImprovementContext):
        improvement = ctx.improvement.text
        parameter = self.visit(ctx.param)
        return Application(Var(improvement), parameter).with_type(t_b)

    # <Integer, Boolean>
    def visitFunction_abstraction(self,
                                  ctx: AeonParser.Function_abstractionContext):
        # I only want the applications list
        _, applications = self.visit(ctx.typee_abstract_parameters())
        return applications

    # (x, 10, f(x))
    def visitCall_parameters(self, ctx: AeonParser.Call_parametersContext):
        return [self.visit(parameter) for parameter in ctx.expression()]


# ------------------------------------------------------------------------------
# -------------------------------- HELPERS -------------------------------------

# --------------------------------
# Returns the name of a given type

    def getBasicTypeName(self, typee):
        if isinstance(typee, BasicType):
            if not self.basic_typee_stack:
                name = '_'
            else:
                name = self.basic_typee_stack.pop()
        elif isinstance(typee, AbstractionType):
            name = typee.arg_name
        elif isinstance(typee, TypeAbstraction):
            name = self.getBasicTypeName(typee.type)
        elif isinstance(typee, TypeApplication):
            name = self.getBasicTypeName(typee.argument)
        else:
            name = typee.name
        return name

    # -----------------------------------------
    # Gets the return type for the Applications
    def getReturnType(self, typee):
        if isinstance(typee, TypeApplication):
            if type(typee.target) is AbstractionType:
                return TypeApplication(typee.target.return_type,
                                       typee.argument)
            else:
                return TypeApplication(self.getReturnType(typee.target),
                                       typee.argument)
        elif isinstance(typee, TypeAbstraction):
            if type(typee.type) is AbstractionType:
                return TypeAbstraction(typee.name, typee.kind,
                                       typee.type.return_type)
            else:
                return TypeAbstraction(typee.name, typee.kind,
                                       self.getReturnType(typee.type))
        elif isinstance(typee, BasicType):
            return typee
        elif isinstance(typee, RefinedType):
            return typee.type
        elif isinstance(typee, AbstractionType):
            return typee.return_type
        else:
            # TODO: problema do refinamento recursivo
            # print(">"*10, "Error in getReturnType with type: ", typee, type(typee))
            return None

    # -----------------------
    # Refines a literal value
    def refined_value(self, v, t, label="_v"):
        operator = Var('==')
        left = Literal(v, t, ensured=True)
        right = Var(label)

        operator = TApplication(operator, t_delegate)
        expression = Application(Application(operator, left), right)

        return RefinedType(name=label, type=t, cond=expression)

    # =========================================================================
    # ---------------------------------------------
    # Distributes each expression through the typee
    def distribute_where_expressions(self, typee, return_name, return_type,
                                     conditions):
        variables = self.functionVariables(typee, return_type)
        variables.add(return_name)
        variables_functions = []

        # Search through all the conditions for their functions and variables
        for cond in conditions:
            # Search variables keeps the variables that exist in the function
            variables_functions.append(
                self.searchVariables(cond, variables, set(), set()))

        # For each set of variables and functions
        for amount, cond in zip(variables_functions, conditions):
            variaveis, functions = amount
            if variaveis:
                return_type = self.apply_expression(variaveis, typee,
                                                    return_name, return_type,
                                                    cond)
            else:
                if functions:
                    variaveis.add(return_name.name)
                    return_type = self.apply_expression(
                        variaveis, typee, return_name, return_type, cond)
                else:
                    print("Error: The given condition: ", cond,
                          " always evaluates to true/false.")
        return return_type

    # Gets all the variables of the function
    def functionVariables(self, typee, return_type):
        variables = set()
        # Guaranteed to be AbstractionType
        while typee != return_type:
            variables.add(typee.arg_name)
            typee = typee.return_type
        return variables

    # Apply a refinement expression to a typee
    def apply_expression(self, variables, typee, return_name, return_type,
                         expression):
        variables.discard(typee.arg_name)
        while variables and typee.return_type != return_type:
            typee = typee.return_type
            variables.discard(typee.arg_name)
        if not variables:
            name = typee.arg_name
            typee.arg_type = self.refine_expression(typee.arg_name,
                                                    typee.arg_type, expression)
        else:
            return_type = self.refine_expression(return_name,
                                                 typee.return_type, expression)
            typee.return_type = return_type
        return return_type

    # Given an typee and an expression, refines it
    def refine_expression(self, name, typee, expression):
        if isinstance(typee, BasicType):
            result = RefinedType(name, typee, expression)
        elif isinstance(typee, AbstractionType):
            result = RefinedType(typee.arg_name, typee, expression)
        elif isinstance(typee, RefinedType):
            and_typee = self.general_context['And']
            application1 = Application(
                Var('And').with_type(and_typee),
                expression).with_type(self.getReturnType(and_typee))
            application2 = Application(application1, typee.cond).with_type(
                self.getReturnType(application1))
            result = RefinedType(typee.name, typee.type, application2)
        elif isinstance(typee, TypeApplication):
            typee.target = self.refine_expression(typee.target, expression)
            result = typee
        elif isinstance(typee, TypeAbstraction):
            typee.type = self.refine_expression(typee.type, expression)
            result = typee
        else:
            result = None
        return result

    # Counts the variables on an expression
    def searchVariables(self, node, variables, set_vars, set_funs):
        if isinstance(node, Hole):
            return set_vars, set_funs
        elif isinstance(node, Literal):
            return set_vars, set_funs
        elif isinstance(node, Var):
            if node.name in variables:
                set_vars.add(node.name)
            else:
                import aeon.libraries.stdlib
                if not aeon.libraries.stdlib.is_builtin(node.name):
                    set_funs.add(node.name)
            return set_vars, set_funs
        elif isinstance(node, If):
            v_cond, f_cond = self.searchVariables(node.cond, variables,
                                                  set_vars, set_funs)
            v_then, f_then = self.searchVariables(node.then, variables,
                                                  set_vars, set_funs)
            v_otherwise, f_otherwise = self.searchVariables(
                node.otherwise, variables, set_vars, set_funs)
            return v_cond | v_then | v_otherwise, f_cond | f_then | f_otherwise
        elif isinstance(node, Application):
            v_target, f_target = self.searchVariables(node.target, variables,
                                                      set_vars, set_funs)
            v_argument, f_argument = self.searchVariables(
                node.argument, variables, set_vars, set_funs)
            return v_target | v_argument, f_target | f_argument
        elif isinstance(node, Abstraction):
            return self.searchVariables(node.body, variables, set_vars,
                                        set_funs)
        elif isinstance(node, TAbstraction):
            return self.searchVariables(node.body, variables, set_vars,
                                        set_funs)
        elif isinstance(node, TApplication):
            return self.searchVariables(node.target, variables, set_vars,
                                        set_funs)
        else:
            return set_vars, set_funs
