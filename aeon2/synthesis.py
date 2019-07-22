import random
import string

from .ast import *
from .types import *
from .substitutions import *
import aeon2.typechecker as tc

forbidden_vars = ['native']


def replicate(v, n):
    return [v for i in range(n)]


def proporcional(elements):
    l = []
    for (p, v) in elements:
        l += replicate(v, p)
    return l


def random_chooser(f):
    def f_alt(*args, **kwargs):
        random.seed(random.randint(0, 1030))
        valid_alternatives = proporcional(f(*args, *kwargs))
        if not valid_alternatives:
            return None
        while True:
            choice = random.choice(valid_alternatives)
            t = choice()
            if t == None:
                continue
            return t

    return f_alt


""" Kind synthesis """


def sk(d=5):
    """ ~> k """
    return star  #TODO
    if random.random() < 0.5 or d < 1:
        return star
    else:
        return Kind(sk(d - 1), sk(d - 1))


""" Type Synthesis """


@random_chooser
def st(ctx, k, d):
    """ Γ ⸠ k ~>_{d} T """
    if k == star:
        yield (1, lambda: t_i)
    if k == star:
        yield (1, lambda: t_b)
    # TODO


def fv(T):
    if type(T) is RefinedType:
        return [T.name] + fv(T.type)
    if type(T) is ArrowType:
        return [T.arg_name] + fv(T.arg_type) + fv(T.return_type)
    return []


def scfv(T):
    """ ~fv(T) ~> t """
    freevars = fv(T)
    print("fv(", T, ") = ", freevars)
    w = ""
    for i in range(1000):
        w += random.choice(string.ascii_letters)
        if w not in freevars:
            return w
    return "_qwerty"


""" Expression Synthesis """


def se_bool(ctx, T, d):
    """ SE-Bool """
    v = random.random() < 0.5
    return Literal(v, type=T)


def se_int(ctx, T, d):
    """ SE-Int """
    v = random.randint(-100, 100)
    return Literal(v, type=T)


def se_if(ctx, T, d):
    """ SE-If """
    cond = se(ctx, t_b, d - 1)
    then = se(ctx, T, d - 1)  # missing refinement in type
    otherwise = se(ctx, T, d - 1)  # missing refinement in type
    return If(cond, then, otherwise).with_type(T)


def se_var(ctx, T, d):
    """ SE-Var """
    options = [
        v for v in ctx.variables
        if tc.is_subtype(ctx, ctx.variables[v], T) and v not in forbidden_vars
    ]
    print("SE-Var", T, options)
    if options:
        n = random.choice(options)
        return Var(n).with_type(T)
    return None


def se_abs(ctx, T: ArrowType, d):
    """ SE-Abs """
    nctx = ctx.with_var(T.arg_name, T.arg_type)
    body = se(nctx, T.return_type, d - 1)
    return Abstraction(T.arg_name, T.arg_type, body).with_type(T)


def se_where(ctx, T: RefinedType, d):
    """ SE-Where """
    e2 = se(ctx, T.type, d - 1)
    ncond = substitution_expr_in_expr(T.cond, e2, T.name)
    if tc.entails(ctx, ncond):
        return e2.with_type(T)


def se_tabs(ctx, T: TypeAbstraction, d):
    """ SE-TAbs """
    nctx = ctx.with_type_var(T.name, T.kind)
    e = se(nctx, T.type, d - 1)
    return TAbstraction(T.name, T.kind, e).with_type(T)


def se_app(ctx, T, d):
    """ SE-App """
    k = sk(d)
    U = st(ctx, k, d - 1)
    x = scfv(T)
    e2 = se(ctx, U, d - 1)
    print("target of type U:", e2, ":", U)
    nctx = ctx.with_type_var(x, U)
    V = stax(nctx, e2, x, T, d - 1)
    FT = ArrowType(arg_name=x, arg_type=U, return_type=V)

    e1 = se(ctx, FT, d - 1)
    print("fun of type:", e1, ":", FT, "should return", T)

    return Application(e1, e2).with_type(T)


@random_chooser
def se(ctx, T, d):
    """ Γ ⸠ T~>_{d} e """
    if type(T) is BasicType and T.name == "Integer":
        yield (1, lambda: se_int(ctx, T, d))
    if type(T) is BasicType and T.name == "Boolean":
        yield (1, lambda: se_bool(ctx, T, d))
    if [v for v in ctx.variables if tc.is_same_type(ctx, ctx.variables[v], T)]:
        yield (100, lambda: se_var(ctx, T, d))
    if d + 100 > 0:
        # TODO
        # yield (1, lambda: se_if(ctx, T, d))
        if type(T) is ArrowType:
            yield (100, lambda: se_abs(ctx, T, d))
        if type(T) is RefinedType:
            yield (100, lambda: se_where(ctx, T, d))
        if type(T) is TypeAbstraction:
            yield (100, lambda: se_tabs(ctx, T, d))
        #yield (1, lambda: se_app(ctx, T, d))
        """ TODO: SE-TApp """


""" Expression Synthesis parameterized with x:T """


def stax_id(nctx, e, x, T, d):
    """ STAx-Id """
    return T


@random_chooser
def stax(nctx, e, x, T, d):
    """ Γ ⸠ T ~>_{d} U """
    yield (1, lambda: stax_id(nctx, e, x, T, d))
    """ TODO: STAx-Arrow """
    """ TODO: STAx-App """
    """ TODO: STAx-Abs """
    """ TODO: STAx-Where """


if __name__ == '__main__':

    from .frontend import expr, typee
    ex = expr.parse_strict
    ty = typee.parse_strict

    d = 3

    def assert_synth(ctx, t, times=3):
        for i in range(times):
            e = se(ctx, t, d)
            tc.tc(ctx, e, t)
            print("Synth'ed:", e, ":", t)
            if e.type != t:
                print("Given type:", e.type)
                print("Expected type", t)
            assert (e.type == t)

    ctx = TypingContext()
    ctx.setup()
    assert_synth(ctx, ty("Boolean"))
    assert_synth(ctx, ty("{x:Boolean where x}"))
    assert_synth(ctx, ty("{x:Boolean where (x === false)}"))
    assert_synth(ctx, ty("Integer"))
    assert_synth(ctx, ty("{x:Integer where (x > 0)}"))
    assert_synth(ctx, ty("{x:Integer where ((x % 4) == 0)}"))

    assert_synth(ctx, ty("(x:Boolean) -> Integer"))
    assert_synth(ctx.with_var("z", ty("(x:Boolean) -> Boolean")),
                 ty("(x:Boolean) -> Boolean"))

    assert_synth(
        ctx.with_var(
            "*",
            tc.
            tc(ctx,
               n=ty(
                   "(x:Integer) -> (y:Integer) -> {z:Integer where (z == (x*y))}"
               ))), ty("(x:Integer) -> {y:Integer where (y == (x*2)) }"))

    print("Passed all tests")
