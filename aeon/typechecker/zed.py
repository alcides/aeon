from functools import reduce

import z3
import math
import random
import logging
import builtins

from ..ast import Var, Literal, Application, Abstraction, TApplication, TAbstraction, Node
from ..types import Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, TypingContext
from ..libraries.stdlib import *
from .substitutions import *
from .zed_utils import *
from .type_simplifier import reduce_type

MAX_Z3_SEEDS = 5


class NotDecidableException(Exception):
    pass


class NoZ3TranslationException(Exception):
    pass


def zed_initial_context():
    return {
        "==": lambda x: lambda y: x == y,
        "!=": lambda x: lambda y: x != y,
        "<": lambda x: lambda y: x < y,
        ">": lambda x: lambda y: x > y,
        "<=": lambda x: lambda y: x <= y,
        ">=": lambda x: lambda y: x >= y,
        "!": lambda x: z3.Not(x),
        "-->": lambda x: lambda y: z3.Implies(x, y),
        "and": lambda x: lambda y: z3.And(x, y),
        "&&": lambda x: lambda y: z3.And(x, y),
        "||": lambda x: lambda y: z3.Or(x, y),
        "+": lambda x: lambda y: x + y,
        "-": lambda x: lambda y: x - y,
        "(-u)": lambda y: -y,
        "*": lambda x: lambda y: x * y,
        "/": lambda x: lambda y: x / y,
        "^": lambda x: lambda y: x ^ y,
        "%": lambda x: lambda y: x % y,
        "smtPow": lambda x: lambda y: x**y,
        "smtAbs": lambda x: z3.If(x < 0, -x, x),
        "smtEq": lambda x: lambda y: x == y,
        "smtIneq": lambda x: lambda y: x != y,
        "smtLt": lambda x: lambda y: x < y,
        "smtGt": lambda x: lambda y: x > y,
        "smtLte": lambda x: lambda y: x <= y,
        "smtGte": lambda x: lambda y: x >= y,
        "smtNot": z3.Not,
        "smtImplies": lambda x: lambda y: z3.Implies(x, y),
        "smtAnd": lambda x: lambda y: z3.And(x, y),
        "smtOr": lambda x: lambda y: z3.Or(x, y),
        "smtPlus": lambda x: lambda y: x + y,
        "smtMinus": lambda x: lambda y: x - y,
        "smtMult": lambda x: lambda y: x * y,
        "smtDiv": lambda x: lambda y: x / y,
        "smtCaret": lambda x: lambda y: x**y,
        "smtMod": lambda x: lambda y: x % y,
        # TODO: delete when everything is working
        "==Int": lambda x: lambda y: x == y,
        "!=Int": lambda x: lambda y: x != y,
        "<Int": lambda x: lambda y: x < y,
        ">Int": lambda x: lambda y: x > y,
        "<=Int": lambda x: lambda y: x <= y,
        ">=Int": lambda x: lambda y: x >= y,
        "+Int": lambda x: lambda y: x + y,
        "-Int": lambda x: lambda y: x - y,
        "*Int": lambda x: lambda y: x * y,
        "/Int": lambda x: lambda y: x / y,
        "^Int": lambda x: lambda y: x**y,
    }


random_name_counter = 0


def random_name():
    global random_name_counter
    random_name_counter += 1
    return "lambda_{}".format(random_name_counter)


def get_sort(t: Type):
    if isinstance(t, BasicType):
        if t.name == 'Integer':
            return z3.IntSort()
        elif t.name == 'Boolean':
            return z3.BoolSort()
        elif t.name == 'Double':
            return z3.RealSort()
        elif t.name == 'String':
            return z3.StringSort()
        elif t.name in ['Top', 'Void', 'Object']:
            return z3.BoolSort()
        else:
            return z3.DeclareSort(t.name)
    elif isinstance(t, RefinedType):
        return get_sort(t.type)
    elif isinstance(t, AbstractionType):
        isort = get_sort(t.arg_type)
        rsort = get_sort(t.return_type)
        return rsort
    elif isinstance(t, TypeApplication):
        return get_sort(t.target)
    elif isinstance(t, TypeAbstraction):
        return get_sort(t.type)
    raise NoZ3TranslationException("No sort for type " + str(t))


class ZedContext(object):
    def __init__(self, initial_context):
        self.variables = initial_context
        self.type_level_conditions = []
        self.top_level_conditions = []
        self.sorts = {}

    def add_top_level(self, r):
        self.top_level_conditions.append(r)

    def get_top_level(self):
        return reduce(z3.And, self.top_level_conditions, True)

    def add_type_level(self, r):
        self.type_level_conditions.append(r)

    def get_type_level(self):
        return reduce(z3.And, self.type_level_conditions, True)

    def get_sort(self, ctx: TypingContext, ty: Type):
        if str(ty) in self.sorts:
            return self.sorts[str(ty)]
        else:
            s = get_sort(ty)
            self.sorts[str(ty)] = s
            return s

    def mk_variable(self, ctx: TypingContext, name: str, ty: Type):
        if name in self.variables:
            return self.variables[name]
        if isinstance(ty, BasicType):
            if ty.name == "Integer":
                return z3.Int(name)
            elif ty.name == 'Double':
                return z3.Real(name)
            elif ty.name == "Boolean":
                return z3.Bool(name)
            elif ty.name == 'String':
                return z3.String(name)
            elif ty.name in ["Top", "Bottom", "Object", "Void"]:
                pass
        elif isinstance(ty, RefinedType):
            v = self.mk_variable(ctx, name, ty.type)
            cond = ty.cond
            if ty.name != name:
                cond = substitution_expr_in_expr(cond, Var(name), ty.name)
            cond_translated = zed_translate(ctx.with_var(name, ty.type), self,
                                            cond)  # TODO: check for context
            self.add_type_level(cond_translated)
            return v  # TODO NOW

        elif isinstance(ty, AbstractionType):
            isort = self.get_sort(ctx, ty.arg_type)
            rsort = self.get_sort(ctx, ty.return_type)
            f = z3.Function(name, isort, rsort)
            return f
        elif isinstance(ty, TypeApplication):
            return self.mk_variable(ctx, name, ty.target)
        elif isinstance(ty, TypeAbstraction):
            return self.mk_variable(ctx, name, ty.type)
        raise NoZ3TranslationException("No constructor for {}:{} \n {}".format(
            name, ty, type(ty)))

    def del_variable(self, name: str):
        del self.variables[name]


# =============================================================================
# Translation of Aeon AST to Z3


def zed_translate_literal(ctx: TypingContext, ztx: ZedContext,
                          literal: Literal):
    if type(literal.value) == str:
        return z3.StringVal(literal.value)
    return literal.value


def zed_translate_type_var(name, ty):
    """
    if isinstance(ty, BasicType):
        return zed_mk_variable(name, ty)
    elif isinstance(ty, AbstractionType):
        return zed_mk_variable(name, reduce_type(None, ty))
    elif isinstance(ty, RefinedType):
        return zed_mk_variable(name, reduce_type(None, ty)) # TODO
    elif isinstance(ty, TypeAbstraction):
        return zed_translate_type_var(name, ty.type)
    """
    raise NoZ3TranslationException("Type not translatable: {} : {}".format(
        name, ty))


def zed_translate_var(ctx: TypingContext, ztx: ZedContext, v: Var):
    assert (isinstance(v, Var))
    if v.name in ctx.variables:
        return ztx.mk_variable(ctx, v.name, ctx.variables[v.name])
    raise NoZ3TranslationException("Var not in scope: {} : {}".format(
        v, v.type))


def zed_translate_if(ctx: TypingContext, ztx: ZedContext, iff: If):
    assert (isinstance(iff, If))
    print("Cond1:", iff)
    cond = zed_translate(ctx, ztx, iff.cond)
    print("Cond:", cond)
    if isinstance(cond, bool):
        if cond:
            return zed_translate(ctx, ztx, iff.then)
        else:
            return zed_translate(ctx, ztx, iff.otherwise)
    else:
        then = zed_translate(ctx, ztx, iff.then)
        otherwise = zed_translate(ctx, ztx, iff.otherwise)
        return z3.If(cond, then, otherwise)


def zed_translate_app(ctx: TypingContext, ztx: ZedContext, app: Application):
    assert (isinstance(app, Application))
    if isinstance(app.target,
                  Var) and app.target.name == 'smtExists' and isinstance(
                      app.argument, Abstraction):
        abstraction = app.argument
        ztx.mk_variable(ctx, abstraction.arg_name, abstraction.arg_type)
        return zed_translate(
            ctx.with_var(abstraction.arg_name, abstraction.arg_type), ztx,
            abstraction.body)

    if isinstance(app.target, Abstraction):
        return zed_translate(
            ctx, ztx,
            substitution_expr_in_expr(app.target.body, app.argument,
                                      app.target.arg_name))

    elif isinstance(app.target, If):
        iif = app.target
        return zed_translate(
            ctx, ztx,
            If(iif.cond, Application(iif.then, app.argument),
               Application(iif.otherwise, app.argument)))
    elif isinstance(app.argument, If):
        iif = app.argument
        return zed_translate(
            ctx, ztx,
            If(iif.cond, Application(app.target, iif.then),
               Application(app.target, iif.otherwise)))

    target = zed_translate(ctx, ztx, app.target)
    argument = zed_translate(ctx, ztx, app.argument)
    return target(argument)


def zed_translate_abs(ctx: TypingContext, ztx: ZedContext, ab: Abstraction):
    assert (isinstance(ab, Abstraction))
    pass
    i_sort = ztx.get_sort(ctx, ab.arg_type)
    o_sort = ztx.get_sort(ctx, ab.body.type)
    f = z3.Function(random_name(), i_sort, o_sort)
    x = ztx.mk_variable(ctx, ab.arg_name, ab.arg_type)
    b = zed_translate(ctx.with_var(ab.arg_name, ab.arg_type), ztx, ab.body)
    ztx.del_variable(ab.arg_name)
    try:
        g = z3.ForAll([x], b)
        ztx.add_top_level(g)
        return f
    except Exception as e:  # TODO NOW2
        logging.debug("Exception unhandled:" + str(e))
        raise NoZ3TranslationException(
            "\{} could not be translated because it is higher order".format(
                ab))


def zed_translate_tabs(ctx: TypingContext, ztx: ZedContext,
                       tabs: TAbstraction):
    assert (isinstance(tabs, TAbstraction))
    return zed_translate(ctx, ztx, tabs.body)


def zed_translate_tapp(ctx: TypingContext, ztx: ZedContext,
                       tapp: TApplication):
    assert (isinstance(tapp, TApplication))
    return zed_translate(ctx, ztx, tapp.target)


# =============================================================================
# Translation from Aeon Types to Z3


def zed_translate(ctx: TypingContext, ztx: ZedContext, cond: Node):
    if isinstance(cond, Application):
        return zed_translate_app(ctx, ztx, cond)
    elif isinstance(cond, Var):
        return zed_translate_var(ctx, ztx, cond)
    elif isinstance(cond, Literal):
        return zed_translate_literal(ctx, ztx, cond)
    elif isinstance(cond, If):
        return zed_translate_if(ctx, ztx, cond)
    elif isinstance(cond, Abstraction):
        return zed_translate_abs(ctx, ztx, cond)
    elif isinstance(cond, TApplication):
        return zed_translate_tapp(ctx, ztx, cond)
    elif isinstance(cond, TAbstraction):
        return zed_translate_tabs(ctx, ztx, cond)
    else:
        raise NoZ3TranslationException(
            "{} could not be translated".format(cond))


def zed_translate_wrapped(ctx, ztx, cond):
    try:
        return zed_translate(ctx, ztx, cond)
    except NoZ3TranslationException as err:
        print("No z3 translation:", err, "for the cond:", cond)
        return True


def extract_from_type(ty):
    if isinstance(ty, BasicType):
        return random_name(), ty, True
    elif isinstance(ty, AbstractionType):
        return random_name(), reduce_type(TypingContext(), ty), True
    elif isinstance(ty, RefinedType):
        t = reduce_type(None, ty)
        return t.name, t.type, t.cond
    elif isinstance(ty, TypeApplication):
        return extract_from_type(ty.target)
    elif isinstance(ty, TypeAbstraction):
        return extract_from_type(ty.type)
    raise NoZ3TranslationException("Type not translatable: {}".format(ty))


def zed_compile_var(ctx: TypingContext, ztx: ZedContext, var_name, type):
    try:
        name, typee, cond = extract_from_type(type)
        ztx.mk_variable(ctx, var_name, typee)
        if cond is not True:
            new_cond = substitution_expr_in_expr(cond, Var(var_name), name)
            return zed_translate_wrapped(ctx, ztx, new_cond)
        # TODO: handle extra_context
    except NoZ3TranslationException as e:
        pass
    return True


def zed_generate_context(ctx: TypingContext, ztx: ZedContext, solver):
    ctx_vars = []

    for var in ctx.variables:
        r_restrictions = zed_compile_var(ctx, ztx, var, ctx.variables[var])

    for i, restriction in enumerate(ctx.restrictions):
        r_var = z3.Bool("#restriction_{}".format(i))
        ztx.add_top_level(
            r_var == zed_translate_wrapped(ctx, ztx, restriction))
        ctx_vars.append(r_var)

    return reduce(z3.And, ctx_vars, True)


def zed_verify_entailment(ctx: TypingContext, cond: TypedNode):
    assert (ctx.inside_refinement)

    s = z3.Solver()

    ztx = ZedContext(zed_initial_context())
    z3_context_restriction = zed_generate_context(ctx, ztx, s)
    z3_cond = zed_translate_wrapped(ctx, ztx, cond)
    s.add(ztx.get_top_level())
    s.add(ztx.get_type_level())
    z3_context = z3.Bool("#context")
    s.add(z3_context == z3_context_restriction)
    s.push()
    if s.check() == z3.unsat:
        return True
    s.pop()
    s.add(z3.And(z3_context, z3.Not(z3_cond)))
    #print("----")
    #print("s:", s)
    for i in range(MAX_Z3_SEEDS):
        r = s.check()

        #print("R:", r)
        if r == z3.unsat:
            return True
        if r == z3.sat:
            #print("Example", s.model())
            return False
        z3.set_option("smt.random_seed", i)
    #print("S:", s, cond, r)
    # S: [x == u%o, ForAll(x, Or(Not(x == u%o), And(x%4 == 0, Not(x <= 2))))]
    #

    raise NotDecidableException(
        "{} could not be evaluated for entailment".format(cond))


def entails(ctx: TypingContext, cond: TypedNode):
    return zed_verify_entailment(ctx, cond)
    """Disable for synthesis:
    cond_type = tc(ctx, cond).type
    if not is_subtype(ctx, cond_type, t_b):
        raise TypeException(
            'Clause not boolean',
            "Condition {}:{} is not a boolean expression".format(cond, cond_type))
    else:
        return zed_verify_entailment(ctx, cond)
    """


def zed_verify_satisfiability(ctx: TypingContext, cond: TypedNode):
    #print(">>>>", cond)
    #ctx.print_ctx()

    ztx = ZedContext(zed_initial_context())
    s = z3.Solver()

    z3_context = zed_generate_context(ctx, ztx, s)
    z3_cond = zed_translate_wrapped(ctx, ztx, cond)

    s.add(z3.And(z3_context, z3_cond))
    r = s.check()
    #print("zed_ver_sat", s, r, 1)
    if r == z3.sat:
        return True
    if r == z3.unsat:
        return False
    raise NotDecidableException(
        "{} could not be evaluated for satisfiability".format(cond))


def is_satisfiable(ctx: TypingContext, cond: TypedNode):
    try:
        return zed_verify_satisfiability(ctx, cond)
    except NotDecidableException as e:
        print(">" * 5, "Not Decidable Exception", cond)
        return True
    except z3.Z3Exception as e:
        print('>' * 5, "Error when translating the condition", cond)
        print(e)
        return True


# TODO: Remove when everything is working
def zed_get_integer_where(ctx: TypingContext, name: str, cond):
    ztx = ZedContext(zed_initial_context())
    s = z3.Solver()

    z3_context = zed_generate_context(ctx, ztx, s)
    z3_cond = zed_translate_wrapped(ctx, ztx, cond)
    s.add(z3.And(z3_context, z3_cond))
    #print("Solver:", s)
    r = s.check()
    if r == z3.sat:
        #print(s.model(), "MODEL")
        m_name = zed_translate(ctx, ztx, Var(name))
        return int(str(s.model()[m_name]))
    else:
        return 1
        # If its impossible, then it does not matter
        raise NotDecidableException(
            "{} could not be evaluated for generating an example".format(cond))
