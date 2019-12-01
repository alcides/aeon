from functools import reduce

import z3
import random

from ..ast import Var, Literal, Application, Abstraction, TApplication, TAbstraction, Node
from ..types import Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b
from ..libraries.stdlib import *
from .substitutions import *
from .zed_utils import *

MAX_Z3_SEEDS = 5


class NotDecidableException(Exception):
    pass


class NoZ3TranslationException(Exception):
    pass


def is_satisfiable(ctx, cond):
    try:
        return zed_verify_satisfiability(ctx, cond)
    except NotDecidableException:
        print("Not Decidable Exception", cond)
        return True


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


random_name_counter = 0


def random_name():
    global random_name_counter
    random_name_counter += 1
    return "lambda_{}".format(random_name_counter)


def flatten_refined_types(t):
    if isinstance(t, RefinedType):
        if type(t.type) is RefinedType:
            inner = t.type
            new_cond = Application(
                Application(Var("&&"), t.cond),
                substitution_expr_in_expr(inner.cond, Var(t.name), inner.name))
            merged = RefinedType(t.name, inner.type, new_cond)
            return flatten_refined_types(merged)
        else:
            return RefinedType(t.name, flatten_refined_types(t.type), t.cond)
    elif isinstance(t, BasicType):
        return t
    elif isinstance(t, AbstractionType):
        return t
    raise NoZ3TranslationException("No Refine Flattening for {} ({})".format(
        t, type(t)))


def zed_mk_variable(name, ty: Type):
    if isinstance(ty, BasicType):
        if ty.name == "Integer":
            return z3.Int(name)
        elif ty.name == "Boolean":
            return z3.Bool(name)
        elif ty.name == "Bottom":
            return z3.Bool(name)
        elif ty.name in ["Top", "Object", "Void"]:
            return z3.Bool(name)
    elif isinstance(ty, RefinedType):
        return zed_mk_variable(name, ty.type)
    elif isinstance(ty, AbstractionType):
        isort = get_sort(ty.arg_type)
        rsort = get_sort(ty.return_type)
        f = z3.Function(name, isort, rsort)
        return f
    raise NoZ3TranslationException("No constructor for {}:{} \n {}".format(
        name, ty, type(ty)))


def zed_translate_literal(ztx, literal: Literal):
    return literal.value


def get_sort(t: Type):
    if isinstance(t, RefinedType):
        return get_sort(t.type)
    if isinstance(t, BasicType):
        if t.name == 'Integer':
            return z3.IntSort()
        elif t.name == 'Boolean':
            return z3.BoolSort()
        elif t.name in ['Top', 'Void', 'Object']:
            return z3.BoolSort()

    raise NoZ3TranslationException("No sort for type " + str(t))


def zed_translate_var(ztx, v: Var):
    if not v.name in ztx:
        if type(v.type) is BasicType:
            ztx[v.name] = zed_mk_variable(v.name, v.type)
            return ztx[v.name]
        elif type(v.type) is AbstractionType:
            #ztx[v.name] = zed_mk_variable(v.name,
            #                              flatten_refined_types(v.type))
            print("TODO: abstype in z3")
        elif type(v.type) is RefinedType:
            ztx[v.name] = zed_mk_variable(v.name,
                                          flatten_refined_types(v.type))
            return ztx[v.name]
        print("ooops", v)
        raise NoZ3TranslationException("Var not in scope: {} : {}".format(
            v, v.type))
    return ztx[v.name]


def zed_translate_app(ztx, app: Application):
    target = zed_translate(ztx, app.target)
    argument = zed_translate(ztx, app.argument)
    return target(argument)


def zed_translate_abs(ztx, ab: Abstraction):
    raise NoZ3TranslationException("Not implemented yet")
    i_sort = get_sort(ab.arg_type)
    o_sort = get_sort(ab.body.type)
    f = z3.Function(random_name(), i_sort, o_sort)
    x = zed_mk_variable(ab.arg_name, ab.arg_type)
    ztx[ab.arg_name] = x
    b = zed_translate(ztx, ab.body)
    del ztx[ab.arg_name]
    g = z3.ForAll([x], b)
    # Add to context
    return f


def zed_translate_tabs(ztx, tabs: TAbstraction):
    # TODO
    raise NoZ3TranslationException("Not implemented yet")
    return tabs.type


def zed_translate_tapp(ztx, tabs: TApplication):
    return zed_translate(ztx, tabs.target)


def zed_translate_type(solver, ztx, name, t):
    if isinstance(t, BasicType):
        ztx[name] = zed_mk_variable(name, t)
        return None
    if isinstance(t, RefinedType):
        ztx[name] = zed_mk_variable(name, flatten_refined_types(t))
        return zed_translate(
            ztx, substitution_expr_in_expr(t.cond, Var(name), t.name))
    else:
        #print("Should have a translation for z3", t) TODO
        return None


def zed_convert_var_to_cond(solver, ztx, ctx, name):
    try:
        return zed_translate_type(solver, ztx, name, ctx.variables[name])
    except NoZ3TranslationException:
        return None


def zed_translate_context(solver, ztx, ctx):
    ctx_var = z3.Bool("#context")

    ctx_vars = []
    for i, restriction in enumerate(ctx.restrictions):
        r_var = z3.Bool("#restriction_{}".format(i))
        solver.add(r_var == zed_translate_wrapped(ztx, restriction))
        ctx_vars.append(r_var)

    for name in ctx.variables.keys():
        r_var = z3.Bool("#var_{}".format(name))
        #print("v:", name, ctx.variables[name])
        var_cond = zed_convert_var_to_cond(solver, ztx, ctx, name)
        if var_cond != None:
            solver.add(r_var == var_cond)
            ctx_vars.append(r_var)
    solver.add(ctx_var == reduce(z3.And, ctx_vars, True))
    return ctx_var


def zed_translate(ztx, cond: Node):
    if isinstance(cond, Application):
        return zed_translate_app(ztx, cond)
    elif isinstance(cond, Var):
        return zed_translate_var(ztx, cond)
    elif isinstance(cond, Literal):
        return zed_translate_literal(ztx, cond)
    elif isinstance(cond, Abstraction):
        return zed_translate_abs(ztx, cond)
    elif isinstance(cond, TApplication):
        return zed_translate_tapp(ztx, cond)
    elif isinstance(cond, TAbstraction):
        return zed_translate_tabs(ztx, cond)
    else:
        raise NoZ3TranslationException(
            "{} could not be translated".format(cond))


def zed_translate_wrapped(ztx, cond):
    try:
        return zed_translate(ztx, cond)
    except NoZ3TranslationException:
        return True


def zed_initial_context():
    return {
        "==": lambda x: lambda y: x == y,
        "!=": lambda x: lambda y: x != y,
        "<": lambda x: lambda y: x < y,
        ">": lambda x: lambda y: x > y,
        "<=": lambda x: lambda y: x <= y,
        ">=": lambda x: lambda y: x >= y,
        "!": z3.Not,
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


def zed_verify_entailment(ctx, cond):
    ztx = zed_initial_context()
    s = z3.Solver()
    z3_context = zed_translate_context(s, ztx, ctx)
    z3_cond = zed_translate_wrapped(ztx, cond)

    s.push()
    s.add(z3_context)
    if s.check() == z3.unsat:
        return True
    s.pop()
    #s.add(z3.And(z3_context, z3.Implies(z3_context, z3_cond)))
    s.add(z3.And(z3_context, z3.Not(z3_cond)))
    #print("zed_ver_entails", cond, "..", s)

    for i in range(MAX_Z3_SEEDS):
        r = s.check()
        #print("R:", r)
        if r == z3.unsat:
            return True
        if r == z3.sat:
            return False
        z3.set_option("smt.random_seed", i)
    print("S:", s, cond, r)
    # S: [x == u%o, ForAll(x, Or(Not(x == u%o), And(x%4 == 0, Not(x <= 2))))]
    #

    raise NotDecidableException(
        "{} could not be evaluated for entailment".format(cond))


def zed_verify_satisfiability(ctx, cond):
    ztx = zed_initial_context()
    s = z3.Solver()

    z3_context = zed_translate_context(s, ztx, ctx)
    z3_cond = zed_translate_wrapped(ztx, cond)
    s.add(z3.And(z3_context, z3_cond))
    r = s.check()
    #print("zed_ver_sat", s, r, 1)
    if r == z3.sat:
        return True
    if r == z3.unsat:
        return False
    raise NotDecidableException(
        "{} could not be evaluated for satisfiability".format(cond))


def zed_get_integer_where(ctx, name, cond):
    ztx = zed_initial_context()
    s = z3.Solver()

    z3_context = zed_translate_context(s, ztx, ctx)
    z3_cond = zed_translate_wrapped(ztx, cond)
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
