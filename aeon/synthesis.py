import random
import string
import sys

from typing import Union, Sequence

from .ast import TypedNode, Var, TAbstraction, TApplication, Application, Abstraction, Literal, Hole, If, Program, \
    TypeDeclaration, TypeAlias, Definition
from .types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_i
from .typechecker.substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from . import typechecker as tc

MAX_TRIES = 10
MAX_TRIES_WHERE = 10

forbidden_vars = ['native', 'uninterpreted', 'if', 'then', 'else']

weights = {
    "sk_star": 1,  # Kinding
    "sk_rec": 0,
    "st_int": 50,  # Terminal types
    "st_bool": 50,
    "st_var": 50,
    "st_where": 1,
    "st_abs": 1,
    "st_tabs": 1,
    "st_tapp": 1,
    "se_int": 50,  # Terminal types
    "se_bool": 50,
    "se_double": 50,
    "se_string": 50,
    "se_var": 45,
    "se_where": 1,
    "se_abs": 1,
    "se_app": 1,
    "se_tabs": 1,
    "se_tapp": 1,
    "se_if": 1,
    "se_subtype": 1,
    "iet_id": 1,
    "iet_abs": 1,
    "iet_where": 1,
    "iet_app": 1,
    "iee_var": 1,
    "iee_id": 1,
    "iee_app": 1,
    "iee_abs": 1,
    "iee_if": 1,
    "iee_tapp": 1,
    "iee_tabs": 1,
    "itt_id": 1,
    "itt_var": 1,
    "itt_abs": 1,
    "itt_where": 1,
    "itt_tapp": 1,
    "itt_tabs": 1,
    "ite_id": 1,
    "ite_app": 1,
    "ite_abs": 1,
    "ite_if": 1,
    "ite_tapp": 1,
    "ite_tabs": 1,
    'ssub_base': 1,
    'ssub_top': 1,
    'ssub_abs': 1,
    'ssub_whereR': 1,
    'ssub_whereL': 1,
    'ssub_tabs': 1,
    'ssub_tapp': 1,
    'ssub_tappL': 1,
    'ssub_tappR': 1,
    'ssup_base': 1,
    'ssup_bottom': 1,
    'ssup_abs': 1,
    'ssup_whereL': 1,
    'ssup_whereL': 1,
    'ssup_tabs': 1,
    'ssup_tapp': 1,
    'ssup_tappL': 1,
    'ssup_tappR': 1,
}


class WeightManager(object):
    def __init__(self, **nw):
        self.nw = nw

    def __enter__(self):
        w = all_disabled()
        for k in self.nw:
            w[k] = self.nw[k]
        set_weights(w)

    def __exit__(self, exception_type, exception_value, traceback):
        reset_weights()


original_weights = weights.copy()


def reset_weights():
    set_weights(original_weights)


def all_disabled():
    w = {k: 1 for k in weights.keys()}
    return w


def set_weights(w):
    for k in w:
        weights[k] = w[k]


class Unsynthesizable(Exception):
    pass


def sum_of_alternative_weights(alts):
    return sum([weights[v[0]] for v in alts])


def pick_one_of(alts):
    total = sum_of_alternative_weights(alts)
    if total <= 0:
        raise Unsynthesizable("No options to pick from:" + str(alts))
    i = random.randint(0, total - 1)
    for (prob, choice) in alts:
        i -= weights[prob]
        if i <= 0:
            return choice
    raise Exception("This line should never happen")


def random_chooser(f):
    def f_alt(*args, **kwargs):
        #random.seed(random.randint(0, 1030))
        rules = ['se_bool', 'se_int', 'se_double', 'se_string', 'se_var']
        if f.__name__ == 'se':
            d = args[2]
            if d < 3:
                for r in rules:
                    weights[r] *= 2

        valid_alternatives = list(f(*args, *kwargs))
        if not valid_alternatives or sum_of_alternative_weights(
                valid_alternatives) <= 0:
            raise Unsynthesizable("No valid alternatives for", f.__name__,
                                  *args)
        old_values = [weights[r] for r in rules]
        for i in range(MAX_TRIES):
            fun = pick_one_of(valid_alternatives)
            try:
                return fun(*args, **kwargs)
            except Unsynthesizable as e:
                for r in rules:
                    weights[r] *= 2
                #if i % 10 == 0:
                #    print("Exception", type(e), str(e))
                pass
                #if i % 10 == 0:
                #    print("Exception:", e, type(e))
                #    print("Failed once to pick using", fun)
            finally:
                for i, r in enumerate(rules):
                    weights[r] = old_values[i]
        raise Unsynthesizable("Too many tries for type: ", *args)

    return f_alt


""" Kind synthesis """


@random_chooser
def sk(d=5):
    """ ~> k """
    yield ("sk_star", lambda d: star)
    if d >= 1:
        yield ("sk_rec", lambda d: Kind(sk(d - 1), sk(d - 1)))


""" Type Synthesis """


def has_type_vars(ctx: TypingContext, k: Kind):
    for v in ctx.type_variables:
        if ctx.type_variables[v] == k:
            return True


def st_int(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Int"
    return t_i


def st_bool(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Bool"
    return t_b


def st_var(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Var"
    options = get_type_variables_of_kind(ctx, k)
    return random.choice(options)


def st_abs(ctx: TypingContext, k: Kind, d: int) -> AbstractionType:
    "ST-Abs"
    x = ctx.fresh_var()
    T = st(ctx, k, d - 1)
    U = st(ctx.with_var(x, T), k, d - 1)
    return AbstractionType(x, T, U)


def st_tabs(ctx: TypingContext, k: Kind, d: int) -> TypeAbstraction:
    "ST-Tabs"
    t = ctx.fresh_var()
    T = st(ctx.with_type_var(t, k.k1), k.k2, d - 1)
    return TypeAbstraction(t, k, T)


def st_tapp(ctx: TypingContext, k: Kind, d: int) -> TypeApplication:
    "ST-Tapp"
    kp = sk(d - 1)
    T = st(ctx, Kind(kp, k), d - 1)
    U = st(ctx, kp, d - 1)
    return TypeApplication(T, U)


@random_chooser
def st(ctx: TypingContext, k: Kind, d: int):
    """ Γ ⸠ k ~>_{d} T """
    if k == star:
        yield ("st_int", st_int)
        yield ("st_bool", st_bool)
        if d > 0:
            yield ("st_abs", st_abs)
    if has_type_vars(ctx, k):
        yield ("st_var", st_var)
    if d > 0:
        if k != star:
            yield ("st_tabs", st_tabs)
        yield ("st_tapp", st_tapp)


def fv(T: Union[Type, TypingContext, TypedNode]):
    if isinstance(T, TypedNode):
        return []  # TODO
    if isinstance(T, TypingContext):
        ctx = T
        return list(ctx.variables.keys()) + list(ctx.type_variables.keys()) + \
                                                 list(ctx.type_aliases.keys())
    if isinstance(T, RefinedType):
        return [T.name] + fv(T.type)
    if isinstance(T, AbstractionType):
        return [T.arg_name] + fv(T.arg_type) + fv(T.return_type)
    return []


def scfv(T: Union[Type, TypingContext], upper: bool = False):
    """ ~fv(T) ~> t """
    # TODO: refactor this with context.freshvar()
    options = upper and string.ascii_uppercase or string.ascii_lowercase
    freevars = fv(T)
    w = ""
    for i in range(1000):
        w += random.choice(options)
        if w not in freevars:
            return w
    return "_qwerty"


def get_variables_of_type(ctx: TypingContext, T: Type):
    return [
        v for v in ctx.variables
        if tc.is_subtype(ctx, ctx.variables[v], T) and v not in forbidden_vars
    ]


def get_type_variables_of_kind(ctx: TypingContext, k: Kind) -> Sequence[Type]:
    rs = []
    for v in ctx.type_variables:
        if ctx.type_variables[v] == k:
            rs.append(BasicType(v))
    return rs


""" Expression Synthesis """


def se_bool(ctx: TypingContext, T: BasicType, d: int):
    """ SE-Bool """
    v = random.random() < 0.5
    name = "lit_{}".format(v)
    return Literal(v,
                   type=RefinedType(name=name,
                                    type=T,
                                    cond=Application(
                                        Application(
                                            TApplication(Var("=="), t_b),
                                            Var(name)),
                                        Literal(value=v,
                                                type=t_b,
                                                ensured=True))))


def se_int(ctx: TypingContext, T: BasicType, d: int):
    """ SE-Int """

    v = round(random.gauss(0, 0.05) * 7500)
    name = "lit_{}".format(v)
    return Literal(v,
                   type=RefinedType(name=name,
                                    type=T,
                                    cond=Application(
                                        Application(
                                            TApplication(Var("=="), t_i),
                                            Var(name)),
                                        Literal(value=v,
                                                type=t_i,
                                                ensured=True))))


def se_double(ctx: TypingContext, T: BasicType, d: int):
    """ SE-Double """
    v = random.gauss(0, 0.05) * 7500
    return Literal(v, T)


def se_string(ctx: TypingContext, T: BasicType, d: int):
    """ SE-String """
    length = random.randint(1, 100)
    v = ''.join(random.choice(string.ascii_letters) for i in range(length))
    return Literal(v, T)


def se_if(ctx: TypingContext, T: Type, d: int):
    """ SE-If """
    e1 = se(ctx, t_b, d - 1)
    e2 = se(ctx.with_cond(e1), T, d - 1)
    e3 = se(ctx.with_cond(Application(Var("!"), e1)), T, d - 1)
    return If(e1, e2, e3).with_type(T)


def se_var(ctx: TypingContext, T: Type, d: int):
    """ SE-Var """
    options = get_variables_of_type(ctx, T)
    if options:
        n = random.choice(options)
        return Var(n).with_type(T)
    raise Unsynthesizable("No var of type {}".format(T))


def se_abs(ctx: TypingContext, T: AbstractionType, d: int):
    """ SE-Abs """
    nctx = ctx.with_var(T.arg_name, T.arg_type)
    body = se(nctx, T.return_type, d - 1)
    return Abstraction(T.arg_name, T.arg_type, body).with_type(T)


def se_app(ctx: TypingContext, T: Type, d: int):
    """ SE-App """
    k = sk(d - 1)
    U = st(ctx, k, d - 1)
    x = ctx.fresh_var()  #scfv(T)
    e2 = se(ctx, U, d - 1)

    nctx = ctx.with_var(x, U)
    V = iet(nctx, e2, x, T, d - 1)
    FT = AbstractionType(arg_name=x, arg_type=U, return_type=V)
    e1 = se(ctx, FT, d - 1)

    return Application(e1, e2).with_type(T)


def se_where(ctx: TypingContext, T: RefinedType, d: int):
    """ SE-Where """
    if T.type == t_i:
        v = tc.get_integer_where(
            ctx.with_var(T.name, T).with_uninterpreted(), T.name, T.cond)
        name = "lit_{}".format(v)
        return Literal(
            v,
            RefinedType(name=name,
                        type=t_i,
                        cond=Application(
                            Application(TApplication(Var("=="), t_i),
                                        Var(name)),
                            Literal(value=v, type=t_i, ensured=True))))

    for _ in range(MAX_TRIES_WHERE):
        e2 = se(ctx, T.type, d - 1)
        ncond = substitution_expr_in_expr(T.cond, e2, T.name)
        if tc.entails(ctx.with_uninterpreted(), ncond):
            return e2  #.with_type(T)

    raise Unsynthesizable(
        "Unable to generate a refinement example: {}".format(T))


def se_tabs(ctx: TypingContext, T: TypeAbstraction, d: int):
    """ SE-TAbs """
    nctx = ctx.with_type_var(T.name, T.kind)
    e = se(nctx, T.type, d - 1)
    return TAbstraction(T.name, T.kind, e).with_type(T)


def se_tapp(ctx: TypingContext, U: TypeApplication, d: int):
    k = sk(d - 1)
    T = st(ctx, k, d - 1)
    t = scfv(ctx, upper=True)
    V = itt(ctx.with_type_var(T, k), T, t, U, d - 1)
    e = se(ctx, AbstractionType(t, k, V), d - 1)
    return TApplication(e, T)


def se_subtype(ctx: TypingContext, T: Type, d: int):
    U = ssub(ctx, T, d - 1)
    return se(ctx, U, d - 1)


@random_chooser
def se(ctx: TypingContext, T: Type, d: int):
    """ Γ ⸠ T~>_{d} e """

    if isinstance(T, BasicType) and T.name == "Integer":
        yield ("se_int", se_int)
    if isinstance(T, BasicType) and T.name == "Boolean":
        yield ("se_bool", se_bool)
    if isinstance(T, BasicType) and T.name == 'String':
        yield ("se_string", se_string)
    if isinstance(T, BasicType) and T.name == 'Double':
        yield ("se_double", se_double)

    if get_variables_of_type(ctx, T):
        yield ("se_var", se_var)
    if d > 0:
        yield ("se_if", se_if)
        if isinstance(T, AbstractionType):
            yield ("se_abs", se_abs)
        if isinstance(T, RefinedType):
            yield ("se_where", se_where)
        if isinstance(T, TypeAbstraction):
            yield ("se_tabs", se_tabs)
        yield ("se_app", se_app)
        if isinstance(T, TypeApplication):
            yield ("se_tapp", se_tapp)
        yield ("se_subtype", se_subtype)


""" Expression Synthesis parameterized with x:T """


def iet_id(ctx: TypingContext, e: TypedNode, x: str, T: Type, d: int):
    """ IET-Id """
    return T


def iet_abs(ctx: TypingContext, e: TypedNode, x: str, AT: AbstractionType,
            d: int):
    """ IET-Abs """
    y = AT.arg_name
    T = AT.arg_type
    U = AT.return_type

    Tp = iet(ctx, e, x, T, d - 1)
    Up = iet(ctx.with_var(y, T), e, x, U, d - 1)
    return AbstractionType(y, Tp, Up)


def iet_where(ctx: TypingContext, e: TypedNode, x: str, RT: RefinedType,
              d: int):
    """  IET-where """
    y = RT.name
    T = RT.type
    e1 = RT.cond
    Tp = iet(ctx, e, x, T, d - 1)
    ncond = iee(ctx.with_var(y, T), e, x, e1, d - 1)
    return RefinedType(y, Tp, ncond)


def iet_app(ctx: TypingContext, e: TypedNode, x: str, TA: TypeApplication,
            d: int):
    """ IET-app """
    T = TA.target
    U = TA.argument
    Tp = iet(ctx, e, x, T, d - 1)
    Up = iet(ctx, e, x, U, d - 1)
    return TypeApplication(Tp, Up)


@random_chooser
def iet(ctx: TypingContext, e: TypedNode, x: str, T: Type, d: int):
    """ Γ ⸠ [e/x] T ~>_{d} U """
    yield ("iet_id", iet_id)
    if isinstance(T, AbstractionType):
        yield ("iet_abs", iet_abs)
    if isinstance(T, TypeApplication):
        yield ("iet_app", iet_app)
    if isinstance(T, RefinedType):
        yield ("iet_where", iet_where)


def iee_var(ctx: TypingContext, ex: TypedNode, x: str, e: TypedNode, d: int):
    """ IEE-Var """
    return Var(x).with_type(e.type)


def iee_id(ctx: TypingContext, ex: TypedNode, x: str, e: TypedNode, d: int):
    """ IEE-Id """
    return e


def iee_app(ctx: TypingContext, ex: TypedNode, x: str, e: Application, d: int):
    """ IEE-App """
    e1 = e.target
    e2 = e.argument
    e1p = iee(ctx, ex, x, e1, d - 1)
    e2p = iee(ctx, ex, x, e2, d - 1)
    return Application(e1p, e2p)


def iee_abs(ctx: TypingContext, ex: TypedNode, x: str, abs: Abstraction,
            d: int):
    """ IEE-Abs """
    y = abs.arg_name
    U = abs.arg_type
    e = abs.body
    Up = iet(ctx, ex, x, U, d - 1)
    ep = iee(ctx.with_var(y, U), ex, x, e, d - 1)
    return Abstraction(y, Up, ep)


def iee_if(ctx: TypingContext, ex: TypedNode, x: str, i: If, d: int):
    """ IEE-If """
    e1 = i.cond
    e2 = i.then
    e3 = i.otherwise
    e1p = iee(ctx, ex, x, e1, d - 1)
    e2p = iee(ctx.with_cond(e1), ex, x, e2, d - 1)
    e3p = iee(ctx.with_cond(Application(Var("!"), e1)), ex, x, e3, d - 1)
    return If(e1p, e2p, e3p)


def iee_tapp(ctx: TypingContext, ex: TypedNode, x: str, tapp: TApplication,
             d: int):
    """ IEE-TApp """
    T = tapp.target
    U = tapp.argument
    Tp = iet(ctx, ex, x, T, d - 1)
    Up = iet(ctx, ex, x, U, d - 1)
    return TApplication(Tp, Up)


def iee_tabs(ctx: TypingContext, ex: TypedNode, x: str, tapp: TAbstraction,
             d: int):
    """ IEE-TAbs """
    T = tapp.body
    Tp = iet(ctx, ex, x, T, d - 1)
    return TAbstraction(tapp.typevar, tapp.kind, Tp)


@random_chooser
def iee(ctx: TypingContext, ex: TypedNode, x: str, e: TypedNode, d: int):
    """ Γ ⸠ [e/x] e ~>_{d} e """
    if e == ex:  # and x not in fv(e):
        yield ("iee_var", iee_var)
    yield ("iee_id", iee_id)
    if isinstance(e, Application):
        yield ("iee_app", iee_app)
    if isinstance(e, Abstraction):
        yield ("iee_abs", iee_abs)
    if isinstance(e, If):
        yield ("iee_if", iee_if)
    if isinstance(e, TApplication):
        yield ("iee_tapp", iee_tapp)
    if isinstance(e, TAbstraction):
        yield ("iee_tabs", iee_tabs)


def check_itt(ctx: TypingContext, T: Type, t: str, U: Type):
    return T == U and \
        t in ctx.type_variables and \
        tc.check_kind(ctx, T, ctx.type_variables[t]) and \
        t not in fv(T)


def itt_id(ctx: TypingContext, T: Type, t: str, U: Type, d: int):
    """ ITT-Id """
    return T


def itt_var(ctx: TypingContext, T: Type, t: str, U: Type, d: int):
    """ ITT-Var """
    return BasicType(t)


def itt_abs(ctx: TypingContext, T: Type, t: str, AT: AbstractionType, d: int):
    """ ITT-Abs """
    y = AT.arg_name
    U = AT.arg_type
    V = AT.return_type

    Up = itt(ctx, T, t, U, d - 1)
    Vp = itt(ctx.with_var(y, U), T, t, V, d - 1)
    return AbstractionType(y, Up, Vp)


def itt_where(ctx: TypingContext, T: Type, t: str, RT: RefinedType, d: int):
    """  ITT-where """
    y = RT.name
    U = RT.type
    e1 = RT.cond
    Up = itt(ctx, T, t, U, d - 1)
    ncond = ite(ctx.with_var(y, U), T, t, e1, d - 1)
    return RefinedType(y, Up, ncond)


def itt_tapp(ctx: TypingContext, T: Type, t: str, TA: TypeApplication, d: int):
    """ ITT-TApp """
    U = TA.target
    V = TA.argument
    Up = itt(ctx, T, t, U, d - 1)
    Vp = itt(ctx, T, t, V, d - 1)
    return TypeApplication(Up, Vp)


def itt_tabs(ctx: TypingContext, T: Type, t: str, TA: TypeAbstraction, d: int):
    """ ITT-TAbs """
    u = TA.name
    k = TA.kind
    U = TA.type
    Up = itt(ctx.with_type_var(u, k), T, t, U, d - 1)
    return TypeAbstraction(u, k, Up)


@random_chooser
def itt(ctx: TypingContext, T: Type, x: str, U: Type, d: int):
    """ Γ ⸠ [T/t] U ~>_{d} V """
    #if check_itt(ctx, T, x, U):
    yield ("itt_id", itt_id)
    yield ("itt_var", itt_var)
    if isinstance(T, AbstractionType):
        yield ("itt_abs", itt_abs)
    if isinstance(T, TypeApplication):
        yield ("itt_tapp", itt_tapp)
    if isinstance(T, TypeAbstraction):
        yield ("itt_tabs", itt_tabs)
    if isinstance(T, RefinedType):
        yield ("itt_where", itt_where)


""" Inverse Type substitution """


def ite_id(ctx: TypingContext, T: Type, t: str, e: TypedNode, d: int):
    """ ITE-Id """
    return e


def ite_app(ctx: TypingContext, T: Type, t: str, e: Application, d: int):
    """ ITE-App """
    e1 = e.target
    e2 = e.argument
    e1p = ite(ctx, T, t, e1, d - 1)
    e2p = ite(ctx, T, t, e2, d - 1)
    return Application(e1p, e2p)


def ite_abs(ctx: TypingContext, T: Type, t: str, a: Abstraction, d: int):
    """ ITE-Abs """
    y = a.arg_name
    U = a.type
    e = a.body
    Up = itt(ctx, T, t, U, d - 1)
    ep = ite(ctx.with_var(y, U), T, t, e, d - 1)
    return Abstraction(y, Up, ep)


def ite_if(ctx: TypingContext, T: type, t: str, i: If, d: int):
    """ ITE-If """
    e1 = i.cond
    e2 = i.then
    e3 = i.otherwise
    e1p = ite(ctx, T, t, e1, d - 1)
    e2p = ite(ctx.with_cond(e1), T, t, e2, d - 1)
    e3p = ite(ctx.with_cond(Application(Var("!"), e1)), T, t, e3, d - 1)
    return If(e1p, e2p, e3p)


def ite_tapp(ctx: TypingContext, T: type, t: str, tapp: TApplication, d: int):
    """ ITE-TApp """
    U = tapp.target
    V = tapp.argument
    Up = itt(ctx, T, t, U, d - 1)
    Vp = itt(ctx, T, t, V, d - 1)
    return TApplication(Up, Vp)


def ite_tabs(ctx: TypingContext, T: type, t: str, tapp: TAbstraction, d: int):
    """ ITE-TAbs """
    U = tapp.body
    Up = itt(ctx, T, t, U, d - 1)
    return TAbstraction(tapp.typevar, tapp.kind, Up)


@random_chooser
def ite(ctx: TypingContext, T: Type, t: str, e: TypedNode, d: int):
    """ Γ ⸠ [T/t] e ~>_{d} e2 """
    yield ("ite_id", ite_id)
    if isinstance(e, Application):
        yield ("ite_app", ite_app)
    if isinstance(e, Abstraction):
        yield ("ite_abs", ite_abs)
    if isinstance(e, If):
        yield ("ite_if", ite_if)
    if isinstance(e, TApplication):
        yield ("ite_tapp", ite_tapp)
    if isinstance(e, TAbstraction):
        yield ("ite_tabs", ite_tabs)


def ssub_base(ctx: TypingContext, T: BasicType, d: int) -> Type:
    """ SSub-Int, SSub-Bool, SSub-Var """
    return T


def ssub_top(ctx: TypingContext, T: Type, d: int) -> Type:
    """ SSub-Top """
    k = sk(d - 1)
    return st(ctx, k, d - 1)


def ssub_abs(ctx: TypingContext, T: AbstractionType,
             d: int) -> AbstractionType:
    """ SSub-Abs """
    U1 = ssup(ctx, T.arg_type, d - 1)
    U2 = ssub(ctx.with_var(T.arg_name, T.arg_type), T.return_type, d - 1)
    return AbstractionType(T.arg_name, U1, U2)


def ssub_whereR(ctx: TypingContext, T: Type, d: int) -> RefinedType:
    """ SSub-WhereR """
    x = ctx.fresh_var()
    U = ssub(ctx, T, d - 1)
    nctx = ctx.with_var(x, U)
    e = se(nctx, t_b, d - 1)
    return RefinedType(x, U, e)
    #if tc.entails(nctx, e):
    #    return RefinedType(x, U, e)
    #raise Unsynthesizable("Subtype where condition is not valid: {}".format(T))


def ssub_whereL(ctx: TypingContext, T: RefinedType, d: int) -> Type:
    """ SSub-whereL """
    nctx = ctx.with_var(T.name, T.type).with_cond(T.cond)
    return ssub(nctx, T.type, d - 1)


def ssub_tabs(ctx: TypingContext, T: TypeAbstraction, d: int) -> Type:
    """ SSub-TAbs """
    U = ssub(ctx.with_type_var(T.name, T.kind), T.type, d - 1)
    return TypeAbstraction(T.name, T.kind, U)


def ssub_tapp(ctx: TypingContext, T: TypeApplication,
              d: int) -> TypeApplication:
    """ SSub-TApp, requires (tU) """
    assert isinstance(T.target, BasicType)
    U = ssub(ctx, T.argument, d - 1)
    return TypeApplication(T.target, U)


def ssub_tappL(ctx: TypingContext, T: TypeApplication, d: int) -> Type:
    """ SSub-TAppL, requires ((∀T:k.U) V) """
    tabs = T.target
    assert isinstance(tabs, TypeAbstraction)
    V = ssub(ctx, substitution_type_in_type(tabs.type, T.argument, tabs.name),
             d - 1)
    return V


def ssub_tappR(ctx: TypingContext, T: Type, d: int) -> TypeApplication:
    """ SSub-TAppR """
    t = ctx.fresh_var()
    k = sk(d - 1)
    V = st(ctx, k, d - 1)
    W = itt(ctx, V, t, T, d - 1)
    U = ssub(ctx, W, d - 1)
    tabs = TypeAbstraction(t, k, U)
    return TypeApplication(tabs, V)


@random_chooser
def ssub(ctx: TypingContext, T: Type, d: int) -> Type:
    #if isinstance(T, BasicType):
    yield ('ssub_base', ssub_base)
    if isinstance(T, BasicType) and T.name == 'Top':
        yield ('ssub_top', ssub_top)
    if d > 0:
        if isinstance(T, AbstractionType):
            yield ('ssub_abs', ssub_abs)
        yield ('ssub_whereR', ssub_whereR)
        if isinstance(T, RefinedType):
            yield ('ssub_whereL', ssub_whereL)
        if isinstance(T, TypeAbstraction):
            yield ('ssub_tabs', ssub_tabs)
        if isinstance(T, TypeApplication) and isinstance(
                T.argument, BasicType):
            yield ('ssub_tapp', ssub_tapp)
        if isinstance(T, TypeApplication) and isinstance(
                T.argument, TypeAbstraction):
            yield ('ssub_tappL', ssub_tappL)
        yield ('ssub_tappR', ssub_tappR)


def ssup_base(ctx: TypingContext, T: Type, d: int) -> Type:
    """ SSup-Int, SSup-Boolean """
    return T


def ssup_bottom(ctx: TypingContext, T: Type, d: int) -> Type:
    """ SSup-Bottom """
    k = sk(d - 1)
    return st(ctx, k, d - 1)


def ssup_abs(ctx: TypingContext, T: AbstractionType,
             d: int) -> AbstractionType:
    """ SSup-Abs """
    U1 = ssub(ctx, T.arg_type, d - 1)
    U2 = ssup(ctx.with_var(T.arg_name, T.arg_type), T.return_type, d - 1)
    return AbstractionType(T.arg_name, U1, U2)


def ssup_whereL(ctx: TypingContext, T: RefinedType, d: int) -> Type:
    """ SSup-WhereL """
    U = ssup(ctx, T.type, d - 1)
    return U


def ssup_whereR(ctx: TypingContext, T: Type, d: int) -> RefinedType:
    """ SSup-WhereR """
    x = ctx.fresh_var()
    U = ssup(ctx, T, d - 1)
    e = se(ctx.with_var(x, U), t_b, d - 1)
    if tc.entails(ctx, e):
        return RefinedType(x, U, e)
    raise Unsynthesizable("Boolean expression did not end up to being true")


def ssup_tabs(ctx: TypingContext, T: TypeAbstraction, d: int) -> Type:
    """ SSup-TAbs """
    U = ssup(ctx.with_type_var(T.name, T.kind), T.type, d - 1)
    return TypeAbstraction(T.name, T.kind, U)


def ssup_tapp(ctx: TypingContext, T: TypeApplication,
              d: int) -> TypeApplication:
    """ SSup-TApp, requires (tU) """
    assert isinstance(T.target, BasicType)
    U = ssup(ctx, T.argument, d - 1)
    return TypeApplication(T.target, U)


def ssup_tappL(ctx: TypingContext, T: TypeApplication, d: int) -> Type:
    """ SSup-TAppL, requires ((∀T:k.U) V) """
    tabs = T.target
    assert isinstance(tabs, TypeAbstraction)
    V = ssup(ctx, substitution_type_in_type(tabs.type, T.argument, tabs.name),
             d - 1)
    return V


def ssup_tappR(ctx: TypingContext, T: Type, d: int) -> TypeApplication:
    """ SSup-TAppR """
    t = ctx.fresh_var()
    k = sk(d - 1)
    V = st(ctx, k, d - 1)
    W = itt(ctx, V, t, T, d - 1)
    U = ssup(ctx, W, d - 1)
    tabs = TypeAbstraction(t, k, U)
    return TypeApplication(tabs, V)


@random_chooser
def ssup(ctx: TypingContext, T: Type, d: int) -> Type:
    yield ('ssup_base', ssup_base)
    if isinstance(T, BasicType) and T.name == 'Bottom':
        yield ('ssup_bottom', ssup_bottom)
    if d > 0:
        if isinstance(T, RefinedType):
            yield ('ssup_whereL', ssup_whereL)
        yield ('ssup_whereR', ssup_whereL)
        if isinstance(T, AbstractionType):
            yield ('ssup_abs', ssup_abs)
        if isinstance(T, TypeAbstraction):
            yield ('ssup_tabs', ssup_tabs)
        if isinstance(T, TypeApplication) and isinstance(
                T.argument, BasicType):
            yield ('ssup_tapp', ssup_tapp)
        if isinstance(T, TypeApplication) and isinstance(
                T.argument, TypeAbstraction):
            yield ('ssup_tappL', ssup_tappL)
        yield ('ssup_tappR', ssup_tappR)
