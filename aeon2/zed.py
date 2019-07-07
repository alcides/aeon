from functools import reduce

import z3

from .types import *
from .ast import *
from .substitutions import *
from .zed_utils import *


class NotDecidableException(Exception):
    pass


class NoZ3TranslationException(Exception):
    pass


def flatten_refined_types(t):
    if type(t) is RefinedType:
        if type(t.type) is RefinedType:
            inner = t.type
            new_cond = App(
                App("&&", t.cond),
                substitution_in_expr(inner.cond, t.name, inner.name))
            merged = RefinedType(t.name, inner.type, new_cond)
            return flatten_refined_types(merged)
        else:
            return RefinedType(t.name, flatten_refined_types(t.type), t.cond)
    elif type(t) is BasicType:
        return t
    elif type(t) is ArrowType:
        return t
    raise Exception("No Refine Flattening for {} ({})".format(t, type(t)))


def zed_mk_variable(name, ty: Type):
    if type(ty) is BasicType:
        if ty.name == "Integer":
            return z3.Int(name)
        elif ty.name == "Boolean":
            return z3.Bool(name)
    raise NoZ3TranslationException("No constructor for {}:{} \n {}".format(
        name, ty, type(ty)))


def zed_translate_literal(ztx, literal: Literal):
    return literal.value


def zed_translate_var(ztx, v: Var):
    if not v.name in ztx:
        if type(v.type) is BasicType:
            ztx[v.name] = zed_mk_variable(v.name,
                                          flatten_refined_types(v.type))
        elif type(v.type) is RefinedType:
            ztx[v.name] = zed_mk_variable(v.name,
                                          flatten_refined_types(v.type))
        else:
            raise NoZ3TranslationException("Var not in scope: {}".format(v))
    return ztx[v.name]


def zed_translate_app(ztx, app: Application):
    target = zed_translate(ztx, app.target)
    argument = zed_translate(ztx, app.argument)
    return target(argument)


def zed_translate_tapp(ztx, app: Application):
    target = zed_translate(ztx, app.target)
    return target


def zed_translate_context(ztx, ctx):
    restrictions = []
    for name in ctx.variables.keys():
        t = ctx.variables[name]
        if type(t) is RefinedType:
            tprime = flatten_refined_types(t)
            new_cond = substitution_in_expr(tprime.cond, Var(name), t.name)
            restrictions.append(new_cond)
    acc = []
    for e in restrictions:
        try:
            acc.append(zed_translate(ztx, e))
        except NoZ3TranslationException:
            pass
    return reduce(z3.And, acc, True)


def zed_translate(ztx, cond):
    if type(cond) is Application:
        return zed_translate_app(ztx, cond)
    elif type(cond) is Var:
        return zed_translate_var(ztx, cond)
    elif type(cond) is Literal:
        return zed_translate_literal(ztx, cond)
    elif type(cond) is TApplication:
        return zed_translate_tapp(ztx, cond)
    else:
        raise NotDecidableException("{} could not be translated".format(cond))


def zed_initial_context():
    return {
        "==": lambda x: lambda y: x == y,
        "!=": lambda x: lambda y: x != y,
        "===": lambda x: lambda y: x == y,
        "!==": lambda x: lambda y: x != y,
        "<": lambda x: lambda y: x < y,
        ">": lambda x: lambda y: x > y,
        "&&": lambda x: lambda y: z3.And(x, y),
        "||": lambda x: lambda y: z3.Or(x, y),
        "<=": lambda x: lambda y: x <= y,
        ">=": lambda x: lambda y: x >= y,
        "+": lambda x: lambda y: x + y,
        "-": lambda x: lambda y: x - y,
    }


def zed_verify_entailment(ctx, cond):
    ztx = zed_initial_context()
    z3_context = zed_translate_context(ztx, ctx)
    z3_cond = zed_translate(ztx, cond)
    relevant_vars = [ztx[str(x)] for x in get_z3_vars(z3_cond)]
    s = z3.Solver()
    s.add(z3.ForAll(relevant_vars, z3.Implies(z3_context, z3_cond)))
    print("SMT Check2:", s)
    r = s.check()
    if r == z3.sat:
        return True
    if r == z3.unsat:
        return False
    raise NotDecidableException("{} could not be evaluated for entailment",
                                cond)


def zed_verify_satisfiability(ctx, cond):
    ztx = zed_initial_context()
    z3_context = zed_translate_context(ztx, ctx)
    z3_cond = zed_translate(ztx, cond)
    s = z3.Solver()
    s.add(z3.And(z3_context, z3_cond))
    print("SMT Check:", s)
    r = s.check()
    if r == z3.sat:
        return True
    if r == z3.unsat:
        return False
    raise NotDecidableException("{} could not be evaluated for satisfiability",
                                cond)
