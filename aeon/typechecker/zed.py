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
        "And": lambda x: lambda y: z3.And(x, y),
        "&&": lambda x: lambda y: z3.And(x, y),
        "||": lambda x: lambda y: z3.Or(x, y),
        "+": lambda x: lambda y: x + y,
        "-": lambda x: lambda y: x - y,
        "*": lambda x: lambda y: x * y,
        "/": lambda x: lambda y: x / y,
        "^": lambda x: lambda y: x ^ y,
        "%": lambda x: lambda y: x % y,
        "smtPow": lambda x: lambda y: math.pow(x, y),
        "smtAbs": lambda x: builtins.abs(x),
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
        "smtCaret": lambda x: lambda y: x ^ y,
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
        "^Int": lambda x: lambda y: x ^ y,
    }


random_name_counter = 0


def random_name():
    global random_name_counter
    random_name_counter += 1
    return "lambda_{}".format(random_name_counter)


def flatten_refined_types(t):
    if isinstance(t, BasicType):
        return t
    elif isinstance(t, AbstractionType):
        return t
    elif isinstance(t, TApplication):
        t.body = flatten_refined_types(t.body)
        return t
    elif isinstance(t, TAbstraction):
        t.target = flatten_refined_types(t.target)
        t.argument = flatten_refined_types(t.argument)
        return t
    elif isinstance(t, RefinedType):
        if type(t.type) is RefinedType:
            inner = t.type
            new_cond = Application(
                Application(Var("&&"), t.cond),
                substitution_expr_in_expr(inner.cond, Var(t.name), inner.name))
            merged = RefinedType(t.name, inner.type, new_cond)
            return flatten_refined_types(merged)
        else:
            return RefinedType(t.name, flatten_refined_types(t.type), t.cond)
    logging.error("No refine flattening for {t}")
    raise NoZ3TranslationException("No Refine Flattening for {} ({})".format(
        t, type(t)))


def zed_mk_variable(name, ty: Type):
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
            return z3.Bool(name)
    elif isinstance(ty, RefinedType):
        return zed_mk_variable(name, ty.type)
    elif isinstance(ty, AbstractionType):
        isort = get_sort(ty.arg_type)
        rsort = get_sort(ty.return_type)
        f = z3.Function(name, isort, rsort)
        return f
    elif isinstance(ty, TApplication):
        return zed_mk_variable(name, ty.target)
    elif isinstance(ty, TAbstraction):
        return zed_mk_variable(name, ty.body)
    raise NoZ3TranslationException("No constructor for {}:{} \n {}".format(
        name, ty, type(ty)))


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
    elif isinstance(t, TApplication):
        return get_sort(t.target)
    elif isinstance(t, TAbstraction):
        return get_sort(t.body)
    raise NoZ3TranslationException("No sort for type " + str(t))


# =============================================================================
# Translation of Aeon AST to Z3


def zed_translate_literal(ctx, ztx, literal: Literal):
    if type(literal.value) == str:
        return z3.StringVal(literal.value)
    return literal.value


def zed_translate_type_var(name, ty):
    if isinstance(ty, BasicType):
        return zed_mk_variable(name, ty)
    elif isinstance(ty, AbstractionType):
        return zed_mk_variable(name, flatten_refined_types(ty))
    elif isinstance(ty, RefinedType):
        return zed_mk_variable(name, flatten_refined_types(ty))
    raise NoZ3TranslationException("Type not translatable: {} : {}".format(
        name, ty))


def zed_translate_var(ctx, ztx, v: Var):
    assert (isinstance(v, Var))

    if not v.name in ztx and v.name in ctx.variables:
        try:
            ztx[v.name] = zed_translate_type_var(v.name, ctx.variables[v.name])
        except NoZ3TranslationException as e:
            raise e
            logging.warning("Warning: ignoring variable {v} in Z3 translation")
            raise NoZ3TranslationException("Var not in scope: {} : {}".format(
                v, v.type))
    return ztx[v.name]


def zed_translate_if(ctx, ztx, iff: If):
    assert (isinstance(iff, If))
    if type(iff.cond) == Literal:
        if iff.cond.value:
            return zed_translate(ctx, ztx, iff.then)
        else:
            return zed_translate(ctx, ztx, iff.otherwise)

    else:
        cond = zed_translate(ctx, ztx, iff.cond)
        then = zed_translate(ctx, ztx, iff.then)
        otherwise = zed_translate(ctx, ztx, iff.otherwise)
        return z3.If(cond, then, otherwise)


def zed_translate_app(ctx, ztx, app: Application):
    assert (isinstance(app, Application))

    if isinstance(app.target, Abstraction):
        return zed_translate(
            ctx, ztx,
            substitution_expr_in_expr(app.target.body, app.argument,
                                      app.target.arg_name))

    target = zed_translate(ctx, ztx, app.target)
    argument = zed_translate(ctx, ztx, app.argument)
    return target(argument)


def zed_translate_abs(ctx, ztx, ab: Abstraction):

    assert (isinstance(ab, Abstraction))

    i_sort = get_sort(ab.arg_type)
    o_sort = get_sort(ab.body.type)
    f = z3.Function(random_name(), i_sort, o_sort)
    x = zed_mk_variable(ab.arg_name, ab.arg_type)
    ztx[ab.arg_name] = x
    b = zed_translate(ctx, ztx, ab.body)
    del ztx[ab.arg_name]
    g = z3.ForAll([x], b)
    # Add to context
    return f


def zed_translate_tabs(ctx, ztx, tabs: TAbstraction):

    assert (isinstance(tabs, TAbstraction))
    return zed_translate(ctx, ztx, tabs.body)


def zed_translate_tapp(ctx, ztx, tapp: TApplication):

    assert (isinstance(tapp, TApplication))
    return zed_translate(ctx, ztx, tapp.target)


# =============================================================================
# Translation from Aeon Types to Z3


def zed_translate(ctx, ztx, cond: Node):
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
        print("No z3 translation:", err)
        return True


def extract_from_type(ty):
    if isinstance(ty, BasicType):
        return random_name(), ty, True
    elif isinstance(ty, AbstractionType):
        return random_name(), flatten_refined_types(ty), True
    elif isinstance(ty, RefinedType):
        t = flatten_refined_types(ty)
        return t.name, t.type, t.cond
    elif isinstance(ty, TypeApplication):
        return extract_from_type(ty.target)
    elif isinstance(ty, TypeAbstraction):
        return extract_from_type(ty.type)
    raise NoZ3TranslationException("Type not translatable: {}".format(ty))


def zed_compile_var(ctx: TypingContext, ztx, var_name, type):
    if var_name in ztx:
        return True
    try:
        name, typee, cond = extract_from_type(type)
        z3_name = zed_mk_variable(var_name, typee)
        ztx[var_name] = z3_name
        if cond is not True:
            new_cond = substitution_expr_in_expr(cond, Var(var_name), name)
            return zed_translate_wrapped(ctx, ztx, new_cond)
    except NoZ3TranslationException as e:
        pass
    return True


def zed_generate_context(ctx: TypingContext, ztx, solver):
    ctx_vars = []

    for var in ctx.variables:
        r_restrictions = zed_compile_var(ctx, ztx, var, ctx.variables[var])
        if r_restrictions is not True:
            ctx_vars.append(r_restrictions)

    for i, restriction in enumerate(ctx.restrictions):
        r_var = z3.Bool("#restriction_{}".format(i))
        solver.add(r_var == zed_translate_wrapped(ctx, ztx, restriction))
        ctx_vars.append(r_var)

    return reduce(z3.And, ctx_vars, True)


def zed_verify_entailment(ctx: TypingContext, cond: TypedNode):
    assert (ctx.inside_refinement)

    s = z3.Solver()

    ztx = zed_initial_context()
    z3_context_restriction = zed_generate_context(ctx, ztx, s)
    z3_cond = zed_translate_wrapped(ctx, ztx, cond)

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
            return False
        z3.set_option("smt.random_seed", i)
    #print("S:", s, cond, r)
    # S: [x == u%o, ForAll(x, Or(Not(x == u%o), And(x%4 == 0, Not(x <= 2))))]
    #

    raise NotDecidableException(
        "{} could not be evaluated for entailment".format(cond))


def entails(ctx, cond):
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


def zed_verify_satisfiability(ctx, cond):

    #print(">>>>", cond)
    #ctx.print_ctx()

    ztx = zed_initial_context()
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


def is_satisfiable(ctx, cond):
    try:
        return zed_verify_satisfiability(ctx, cond)
    except NotDecidableException as e:
        print(">" * 5, "Not Decidable Exception", cond)
        return True


# TODO: Remove when everything is working
def zed_get_integer_where(ctx, name, cond):
    ztx = zed_initial_context()
    s = z3.Solver()

    z3_context = zed_generate_context(ctx, ztx, s)
    z3_cond = zed_translate_wrapped(ctx, ztx, cond)
    s.add(z3.And(z3_context, z3_cond))
    #print("Solver:", s)
    r = s.check()
    if r == z3.sat:
        #print(s.model(), "MODEL")
        m_name = zed_translate(ztx, Var(name))
        return int(str(s.model()[m_name]))
    else:
        return 1
        # If its impossible, then it does not matter
        raise NotDecidableException(
            "{} could not be evaluated for generating an example".format(cond))
