from .typestructure import *
from .ast import *
from .zed import zed


class TypeException(Exception):
    def __init__(self,
                 name,
                 description="",
                 given=None,
                 expected=None,
                 *args,
                 **kwargs):
        super(TypeException, self).__init__(name, description, *args, **kwargs)
        self.expected = expected
        self.given = given


class TypeContext(object):
    def __init__(self, typedecl=None, refined=True):
        self.types = typedecl and typedecl or []
        self.type_aliases = {}
        self.refined = refined
        self.free_vars = []
        self.setUpBasicTypes()

    def setUpBasicTypes(self):
        self.types.append(BasicType('Void'))
        self.types.append(BasicType('Integer'))
        self.types.append(BasicType('Double'))
        self.types.append(BasicType('Boolean'))
        self.types.append(BasicType('String'))

    def add_type(self, t):
        self.types.append(t)

    def add_type_alias(self, t1, t2):
        self.type_aliases[t1] = t2.copy()

    def handle_aliases(self, t):
        for k in self.type_aliases.keys():
            t = t.replace_type(k, self.type_aliases[k])
        return t

    def is_same_type(self, t1, t2):
        if t2 == t_v:
            return True
        elif type(t1) is BasicType and type(t2) is BasicType:
            return t1.basic == t2.basic or (t1.basic == t_i.basic
                                            and t2.basic == t_f.basic)
        elif type(t1) is BasicType and type(t2) is ParametricType:
            return False
        elif type(t1) is ParametricType and type(t2) is BasicType:
            return False
        elif type(t1) is ParametricType and type(t2) is ParametricType:
            return self.is_same_type(t1.basic, t2.basic) and all([
                is_same_type(a, b)
                for a, b in zip(t1.type_arguments, t2.type_arguments)
            ])
        else:
            print("unknown t, polymorphic or function type checking")
            return False

    def is_subtype(self, t1, t2, context):
        t1 = self.handle_aliases(t1)
        t2 = self.handle_aliases(t2)
        if self.refined:
            return self.is_same_type(t1, t2) and zed.is_subtype(
                t1, t2, context, self)
        else:
            return self.is_same_type(t1, t2)

    def find_substitution_for(self, t1, t2):
        t1 = self.handle_aliases(t1)
        t2 = self.handle_aliases(t2)
        return find_substitution_for(t1, t2)


class Context(object):
    def __init__(self, tcontext):
        self.stack = []
        self.typecontext = tcontext
        self.push_frame()
        self.functions = {}

    def push_frame(self):
        self.stack.append({})

    def push_frame(self):
        self.stack.append({})

    def pop_frame(self):
        self.stack = self.stack[:-1]

    def find(self, kw):
        for frame in self.stack[::-1]:
            if kw in frame:
                return self.typecontext.handle_aliases(frame[kw])
        return None

    def set(self, k, v):
        self.stack[-1][k] = v

    def variables(self):
        vs = []
        for s in self.stack[::-1]:
            vs += s.keys()
        return vs


class TypeChecker(object):
    def __init__(self, root, refined=True, synthesiser=None):
        self.typecontext = TypeContext(refined=refined)
        self.context = Context(self.typecontext)
        self.refined = refined
        self.root = root
        self.synthesiser = synthesiser

    def type_error(self, string, expected=None, given=None):
        raise TypeException("Type Error",
                            string,
                            expected=expected,
                            given=given)

    def is_subtype(self, a, b, *args, **kwargs):
        if b == None:
            return True
        return self.typecontext.is_subtype(a, b, self.context, *args, **kwargs)

    def typecheck_program(self, n):
        for e in n.declarations:
            self.typecheck(e)
        return n

    def typecheck_typedecl(self, n):
        n.type.add_properties(n.properties)
        n.type.add_refinements(n.refinements)
        self.typecontext.add_type_alias(n.alias, n.type)
        return n

    def typecheck_functiondecl(self, n):

        # Step 1: Gather parts

        ret_name = n.return_value.name
        ret_type = n.return_value.type

        parameter_types = list(map(lambda x: (x.name, x.type), n.parameters))
        convert_parameter = lambda i, x: x[1].copy().replace_vars(mapping)

        mapping = {ret_name: "__return"}
        for i, (name, _) in enumerate(parameter_types):
            mapping[name] = "__arg_{}".format(i)

        # Step 2: Prepare function type

        fun_type = FunctionType(
            return_type=ret_type.copy().replace_vars(mapping),
            parameter_types=[
                convert_parameter(i, n) for i, n in enumerate(parameter_types)
            ],
            refinements=n.refinements).copy()

        if n.type_parameters:
            fun_type = PolyType(binders=n.type_parameters, term=fun_type)
            self.typecontext.free_vars = list(n.type_parameters)

        fun_type.replace_vars(mapping)

        self.context.functions[n.name] = fun_type

        # Step 2: Verify wheres
        self.context.push_frame()

        for name, t in parameter_types:
            self.context.set(name, t)

        self.context.set(ret_name, ret_type)
        for refinement in n.refinements:
            self.typecheck_expr(refinement, expects=t_b)

        del self.context.stack[-1][ret_name]  # pop return variable

        # Step 3: Verify body

        if n.body:

            body_complete_type = ret_type.copy()
            body_complete_type.add_refinements(n.refinements)
            self.typecheck_expr(n.body, expects=body_complete_type)

        self.context.pop_frame()
        self.typecontext.free_vars = []

        return n

    def typecheck_op(self, n, expects=None):
        if n.name in ['&&', '||']:
            n.type = t_b
            self.typecheck_expr(n.arguments[0], expects=t_b)
            self.typecheck_expr(n.arguments[1], expects=t_b)

        elif n.name in ["<", "<=", ">", ">=", "==", "!="]:
            n.type = t_b
            self.typecheck_expr(n.arguments[0], expects=t_f)
            self.typecheck_expr(n.arguments[1], expects=t_f)
        elif n.name in ["+", "-", "*", "/", "%"]:
            self.typecheck_expr(n.arguments[0], expects=t_f)
            self.typecheck_expr(n.arguments[1], expects=t_f)
            n.type = t_i if all([k.type == t_i for k in n.arguments]) else t_f
        else:
            self.type_error("Unknown operator {}".format(n))

    def typecheck_block(self, n, expects=None):
        if not n.expressions:
            n.type = t_v
        else:
            for i in n.expressions[:-1]:
                self.typecheck_expr(i)
            self.typecheck_expr(n.expressions[-1], expects=expects)
            n.type = n.expressions[-1].type
        return n

    def typecheck_invocation(self, n, expects=None):
        fundb = self.context.functions

        if not n.name in fundb:
            self.type_error("Undefined function {} in {}".format(n.name, n))

        for arg in n.arguments:
            self.typecheck_expr(arg)

        fun_type = fundb[n.name]
        candidate_type = FunctionType(
            return_type=expects or BasicType('Any'),
            parameter_types=[arg.type for arg in n.arguments])

        c = self.typecontext.find_substitution_for(candidate_type, fun_type)
        print("c:", c, candidate_type, fun_type)

        # Step 1. Check arguments
        for arg, argt in zip(n.arguments, fun_type.parameter_types):
            self.typecheck_expr(arg, expects=argt)

        # Step 2. Assign type
        n.type = fun_type.return_type
        if n.type.is_subtype_of(fun_type.return_type):
            return n
        else:
            self.type_error("Function {} returns wrong type.",
                            given=n.type,
                            expected=expects)

    def typecheck_let(self, n, expects=None):
        if n.type:
            self.context.set(n.name, n.type)
            expected_type_in_let = n.type
            if expects and not self.is_subtype(expected_type_in_let, expects):
                self.type_error("Let has wrong type.",
                                given=expected_type_in_let,
                                expected=expects)
            self.typecheck_expr(n.body, expects=expected_type_in_let)
        else:
            self.typecheck_expr(n.body, expects=expects)
            n.type = n.body.type
            self.context.set(n.name, n.type)

    def typecheck_lambda(self, n, expects=None):
        self.context.push_frame()
        parameter_types = list(map(lambda x: (x.name, x.type), n.parameters))
        for name, t in parameter_types:
            self.context.set(name, t)
        self.typecheck_expr(n.body)
        self.context.pop_frame()

        n.type = FunctionType(return_type=n.body.type,
                              parameter_types=[a.type for a in n.parameters])

        if expects != None:
            if not self.is_subtype(n.type, expects):
                self.type_error("Lambda has wrong type.",
                                given=n.type,
                                expected=expects)
        return n

    def find_variable(self, name):
        f = self.context.find(name)
        if f:
            return f
        if "." in name:
            first_part = name.split(".")[0]
            second_part = name.split(".")[-1]
            f = self.context.find(first_part)
            if f:
                for prop in f.get_properties():
                    if prop.name == second_part:
                        return prop.type
        return False

    def typecheck_atom(self, n, expects=None):
        varname = n.name
        f = self.find_variable(varname)
        if not f:
            self.type_error("Undefined variable {} in {}".format(varname, n))
        n.type = f
        return n

    def typecheck_argument(self, n, expects=None):
        return n

    def typecheck_literal(self, n, expects=None):
        if self.refined:
            n.type.refined = zed.make_literal(n.type, n)
            n.type.context = zed.copy_assertions()
            n.type.conditions = [
                Operator('==', Atom('self'), Literal(n, type=n.type.basic))
            ]
        else:
            pass

    def typecheck_expr(self, n, expects=None):
        if type(n) is Operator:
            self.typecheck_op(n, expects)
        elif type(n) is Atom:
            self.typecheck_atom(n, expects)
        elif type(n) is Argument:
            self.typecheck_argument(n)
        elif type(n) is Literal:
            self.typecheck_literal(n)
        elif type(n) is Block:
            self.typecheck_block(n, expects)
        elif type(n) is Let:
            self.typecheck_let(n, expects)
        elif type(n) is LambdaExpression:
            self.typecheck_lambda(n, expects)
        elif type(n) is Invocation:
            self.typecheck_invocation(n, expects)
        else:
            self.type_error("Unknown expr node {} ({})".format(n, type(n)))

        if expects != None and not self.is_subtype(n.type, expects):
            self.type_error("Node {} has incorrect type.".format(n),
                            given=n.type,
                            expected=expects)
        return n

    def typecheck(self, n):
        if type(n) is Program:
            return self.typecheck_program(n)
        elif type(n) is TypeDecl:
            return self.typecheck_typedecl(n)
        elif type(n) is FunctionDecl:
            return self.typecheck_functiondecl(n)
        else:
            print("TypeChecking undefined for {}".format(type(n)))

        return n


def typecheck(ast, refined=True, synthesiser=None):
    tc = TypeChecker(ast, refined=refined, synthesiser=synthesiser)
    return tc.typecheck(ast), tc.context, tc.typecontext
