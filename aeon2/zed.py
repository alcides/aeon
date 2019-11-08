from functools import reduce

import z3
import random

from .ast import Var, Literal, Application, Abstraction, TApplication, TAbstraction, Node
from .types import Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b
from .stdlib import *
from .substitutions import *
from .zed_utils import *

MAX_Z3_SEEDS = 5


class NotDecidableException(Exception):
    pass


class NoZ3TranslationException(Exception):
    pass


random_name_counter = 0


def random_name():
    global random_name_counter
    random_name_counter += 1
    return "lambda_{}".format(random_name_counter)


def flatten_refined_types(t):
    if type(t) is RefinedType:
        if type(t.type) is RefinedType:
            inner = t.type
            new_cond = Application(
                Application(Var("&&"), t.cond),
                substitution_expr_in_expr(inner.cond, Var(t.name), inner.name))
            merged = RefinedType(t.name, inner.type, new_cond)
            return flatten_refined_types(merged)
        else:
            return RefinedType(t.name, flatten_refined_types(t.type), t.cond)
    elif type(t) is BasicType:
        return t
    elif type(t) is AbstractionType:
        return t
    raise NoZ3TranslationException("No Refine Flattening for {} ({})".format(
        t, type(t)))


def zed_mk_variable(name, ty: Type):
    if type(ty) is BasicType:
        if ty.name == "Integer":
            return z3.Int(name)
        elif ty.name == "Boolean":
            return z3.Bool(name)
        elif ty.name == "Bottom":
            return z3.Bool(name)
        elif ty.name in ["Top", "Object", "Void"]:
            return z3.Bool(name)
    elif type(ty) is RefinedType:
        return zed_mk_variable(name, ty.type)
    elif type(ty) is AbstractionType:
        isort = get_sort(ty.arg_type)
        rsort = get_sort(ty.return_type)
        f = z3.Function(name, isort, rsort)
        return f
    raise NoZ3TranslationException("No constructor for {}:{} \n {}".format(
        name, ty, type(ty)))


def zed_translate_literal(ztx, literal: Literal):
    return literal.value


def get_sort(t: Type):
    if type(t) is RefinedType:
        return get_sort(t.type)
    if type(t) is BasicType:
        if t.name == 'Integer':
            return z3.IntSort()
        elif t.name == 'Boolean':
            return z3.IntSort()
        elif t.name in ['Top', 'Void', 'Object']:
            return z3.BoolSort()

    raise NoZ3TranslationException("No sort for type " + str(t))


def zed_translate_var(ztx, v: Var):
    if not v.name in ztx:
        if type(v.type) is BasicType:
            print("ex: v.name=", v.name)
            ztx[v.name] = zed_mk_variable(v.name,
                                          flatten_refined_types(v.type))
        elif type(v.type) is AbstractionType:
            ztx[v.name] = zed_mk_variable(v.name,
                                          flatten_refined_types(v.type))

        elif type(v.type) is RefinedType:
            print("rx: v.name=", v.name)
            ztx[v.name] = zed_mk_variable(v.name,
                                          flatten_refined_types(v.type))
        else:
            raise NoZ3TranslationException("Var not in scope: {} : {}".format(
                v, v.type))
    return ztx[v.name]


def zed_translate_app(ztx, app: Application):
    target = zed_translate(ztx, app.target)
    argument = zed_translate(ztx, app.argument)
    return target(argument)


def zed_translate_abs(ztx, ab: Abstraction):

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


def zed_translate_tabs(ztx, tabs: TypeAbstraction):
    return tabs.type


def zed_translate_tapp(ztx, tabs: TypeApplication):
    return tabs.target


def zed_translate_context(ztx, ctx):
    restrictions = []
    for name in ctx.variables.keys():
        t = ctx.variables[name]
        try:
            if name not in ztx:
                ztx[name] = zed_mk_variable(name, flatten_refined_types(t))
            if type(t) is RefinedType:
                tprime = flatten_refined_types(t)
                new_cond = substitution_expr_in_expr(tprime.cond, Var(name),
                                                     t.name)
                restrictions.append(new_cond)
        except NoZ3TranslationException:
            continue
    acc = []
    for e in restrictions:
        c = zed_translate_wrapped(ztx, e)
        acc.append(c)
    return reduce(z3.And, acc, True)


def zed_translate(ztx, cond: Node):
    if type(cond) is Application:
        return zed_translate_app(ztx, cond)
    elif type(cond) is Var:
        return zed_translate_var(ztx, cond)
    elif type(cond) is Literal:
        return zed_translate_literal(ztx, cond)
    elif type(cond) is Abstraction:
        return zed_translate_abs(ztx, cond)
    elif type(cond) is TApplication:
        return zed_translate_tapp(ztx, cond)
    elif type(cond) is TAbstraction:
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
    c = {}
    for name in get_all_builtins():
        f = get_builtin_z3_function(name)
        if f:
            c[name] = get_builtin_z3_function(name)
    return c


def zed_verify_entailment(ctx, cond):
    ztx = zed_initial_context()
    z3_context = zed_translate_context(ztx, ctx)
    z3_cond = zed_translate_wrapped(ztx, cond)
    relevant_vars = [ztx[str(x)] for x in get_z3_vars(z3_cond)]
    s = z3.Solver()
    if relevant_vars:
        s.add(z3_context)
        s.add(z3.ForAll(relevant_vars, z3.Implies(z3_context, z3_cond)))
    else:
        s.add(z3_context)
        s.add(z3.Implies(z3_context, z3_cond))
    #print("zed_ver_entails", s)

    for i in range(MAX_Z3_SEEDS):
        r = s.check()
        if r == z3.sat:
            return True
        if r == z3.unsat:
            return False
        z3.set_option("smt.random_seed", i)
    print("S:", s, cond, r)
    # S: [x == u%o, ForAll(x, Or(Not(x == u%o), And(x%4 == 0, Not(x <= 2))))]
    #

    raise NotDecidableException(
        "{} could not be evaluated for entailment".format(cond))


def zed_verify_satisfiability(ctx, cond):
    ztx = zed_initial_context()
    z3_context = zed_translate_context(ztx, ctx)
    z3_cond = zed_translate_wrapped(ztx, cond)
    s = z3.Solver()
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
    z3_context = zed_translate_context(ztx, ctx)
    z3_cond = zed_translate_wrapped(ztx, cond)
    s = z3.Solver()
    s.add(z3.And(z3_context, z3_cond))
    r = s.check()
    if r == z3.sat:
        print(s.model(), "MODEL")
        m_name = zed_translate(ztx, Var(name))
        return s.model()[m_name]
    else:
        raise NotDecidableException(
            "{} could not be evaluated for generating an example".format(cond))
