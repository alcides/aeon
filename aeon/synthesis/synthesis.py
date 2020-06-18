import random
import string
import sys
import logging

from typing import Union, Sequence, Optional, List, Generator, Tuple, Any

from aeon.ast import TypedNode, Var, TAbstraction, TApplication, Application, Abstraction, Literal, Hole, If, Program, \
    TypeDeclaration, TypeAlias, Definition
from aeon.types import TypingContext, Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b, t_i, t_f, t_s
from aeon.typechecker.substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from aeon.typechecker.typing import TypeCheckingError
from aeon import typechecker as tc

from aeon.synthesis.utils import flatten_refined_type, filter_refinements
from aeon.synthesis.ranges import try_ranged, RangedContext, RangedException

MAX_TRIES = 3
MAX_TRIES_WHERE = 100

forbidden_vars = ['native', 'uninterpreted', 'if', 'then', 'else', 'print']

weights = {
    "sk_star": 1,  # Kinding
    "sk_rec": 0,
    "st_int": 50,  # Terminal types
    "st_bool": 50,
    "st_double": 50,
    "st_string": 50,
    "st_var": 50,
    "st_where": 1,
    "st_abs": 6,
    "st_tabs": 1,
    "st_tapp": 1,
    "se_int": 100,  # Terminal types
    "se_bool": 1,
    "se_double": 1,
    "se_string": 1,
    "se_var": 5,
    "se_where": 1,
    "se_abs": 1,
    "se_app": 1,
    "se_tabs": 0,
    "se_tapp": 0,
    "se_if": 1,
    "se_subtype": 1,
    "iet_id": 1,
    "iet_abs": 1,
    "iet_where": 1,
    "iet_tapp": 1,
    "iet_tabs": 1,
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
    'ssup_whereR': 1,
    'ssup_tabs': 1,
    'ssup_tapp': 1,
    'ssup_tappL': 1,
    'ssup_tappR': 1,
    # Pool of Genetic Material
    'se_genetics': 0,
}

genetic_material: List[TypedNode] = []


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


def set_genetics(material: List[TypedNode]):
    weights['se_genetics'] = len(material)
    genetic_material.extend(material)


def reset_genetics():
    genetic_material = []
    weights['se_genetics'] = 0


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
        actual_max_tries = MAX_TRIES
        rules = ['se_bool', 'se_int', 'se_double', 'se_string', 'se_var']
        old_values = [weights[r] for r in rules]
        if f.__name__ == 'se':
            d = args[2]
            if d < 3:
                actual_max_tries = MAX_TRIES
                for r in rules:
                    weights[r] *= 100
        #print(args, "#", kwargs, "#", list(f(*args, *kwargs)))
        valid_alternatives = list(f(*args, *kwargs))
        logging.info("args: {}".format(", ".join([str(x) for x in args])))
        logging.info("options in random_chooser: {}".format(", ".join(
            [x[0] for x in valid_alternatives])))
        if not valid_alternatives or sum_of_alternative_weights(
                valid_alternatives) <= 0:
            raise Unsynthesizable("No valid alternatives for", f.__name__,
                                  *args)
        for i in range(actual_max_tries):
            fun = pick_one_of(valid_alternatives)
            try:
                logging.info("Chosen: {}".format(fun.__name__))
                v = fun(*args, **kwargs)
                if f.__name__ == 'se':
                    #print("checking", args[0], v, args[1])
                    tc.check_type(args[0], v, args[1])
                return v
            except Unsynthesizable as e:
                logging.info(
                    "random_chooser/d: failed restriction: {}".format(e))
                for r in rules:
                    weights[r] *= 100
                #print("Exception", type(e), str(e))
                #if i % 10 == 0:
                #print("Exception:", e) #, type(e))
                #print("Failed once to pick using", fun)
                pass
            finally:
                for i, r in enumerate(rules):
                    weights[r] = old_values[i]
        raise Unsynthesizable("Too many tries for type: ", *args)

    return f_alt


""" Genetic synthesis """


def get_valid_genetics(ctx: TypingContext, T: Type, d: int):
    result = []

    for tree in genetic_material:
        has_valid_size = d - tree.get_height() >= 0
        has_valid_type = tc.is_subtype(ctx, tree.type, T)

        if has_valid_size and has_valid_type:
            result.append(tree)

    return result


def se_genetics(ctx: TypingContext, T: Type, d: int):
    logging.info("se_genetics/{}: {} ".format(d, T))
    valid_alternatives = get_valid_genetics(ctx, T, d)
    choice = random.choice(valid_alternatives)
    genetic_material.remove(choice)
    weights['se_genetics'] -= 1
    return choice


""" Kind synthesis """


def sk(d=5):
    logging.info("sk")
    """ ~> k """
    if d == 0 or random.random() < 0.7:
        return star
    else:
        return Kind(sk(d - 1), sk(d - 1))


""" Type Synthesis """


def has_type_vars(ctx: TypingContext, k: Kind):
    for v in ctx.type_variables:
        if ctx.type_variables[v] == k:
            return True


def st_int(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Int"
    logging.info("st_int")
    return t_i


def st_bool(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Bool"
    logging.info("st_bool")
    return t_b


def st_double(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Double"
    logging.info("st_double")
    return t_f


def st_string(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-String"
    logging.info("st_string")
    return t_s


def st_var(ctx: TypingContext, k: Kind, d: int) -> Type:
    "ST-Var"
    options = get_type_variables_of_kind(ctx, k)
    logging.info("st_var")
    logging.info("options:" + str(options))
    return random.choice(options)


def st_abs(ctx: TypingContext, k: Kind, d: int) -> AbstractionType:
    "ST-Abs"
    logging.info("st_abs/{}: {} ".format(d, k))
    x = ctx.fresh_var()
    T = st(ctx, k, d - 1)
    U = st(ctx.with_var(x, T), k, d - 1)
    return AbstractionType(x, T, U)


def st_where(ctx: TypingContext, k: Kind, d: int) -> RefinedType:
    "ST-Where"
    logging.info("st_where/{}: {} ".format(d, k))
    x = ctx.fresh_var()
    T = st(ctx, k, d - 1)
    e = se(ctx.with_var(x, T), BasicType('Boolean'), d - 1)
    return RefinedType(x, T, e)


def st_tabs(ctx: TypingContext, k: Kind, d: int) -> TypeAbstraction:
    "ST-Tabs"
    assert (k != star)
    logging.info("st_tabs/{}: {} ".format(d, k))
    t = ctx.fresh_var()
    T = st(ctx.with_type_var(t, k.k1), k.k2, d - 1)
    return TypeAbstraction(t, k, T)


def st_tapp(ctx: TypingContext, k: Kind, d: int) -> TypeApplication:
    "ST-Tapp"
    logging.info("st_tapp/{}: {} ".format(d, k))
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
        yield ("st_double", st_double)
        yield ("st_string", st_string)
        if d > 0:
            yield ("st_abs", st_abs)
            yield ("st_where", st_where)
    if has_type_vars(ctx, k):
        yield ("st_var", st_var)
    if d > 0:
        if k != star:
            yield ("st_tabs", st_tabs)
        yield ("st_tapp", st_tapp)


def is_compatible(ctx: TypingContext, v: str, T: Type):
    try:
        return v not in forbidden_vars and tc.is_subtype(
            ctx, ctx.variables[v], T)
    except Exception as e:
        return False


def get_variables_of_type(ctx: TypingContext, T: Type):
    return [v for v in ctx.variables if is_compatible(ctx, v, T)]


def get_type_variables_of_kind(ctx: TypingContext, k: Kind) -> Sequence[Type]:
    rs = []
    for typee, kind in ctx.type_variables.items():
        if kind == k and typee not in ['Bottom', 'Void']:
            rs.append(BasicType(typee))
    return rs


""" Expression Synthesis """


# Refines a literal expression
def refine_literal(value, typee: Type, label) -> RefinedType:

    operator = TApplication(Var('=='), typee)
    left = Literal(value, typee, ensured=True)
    right = Var(label)

    condition = Application(Application(operator, right), left)

    return RefinedType(name=label, type=typee, cond=condition)


def se_bool(ctx: TypingContext, T: BasicType, d: int) -> TypedNode:
    """ SE-Bool """
    assert (isinstance(T, BasicType))

    value = random.choice([True, False])

    logging.info("se_bool/{}: {}:{} ".format(d, value, T))
    return Literal(value, refine_literal(value, T, '_b'))


def se_int(ctx: TypingContext, T: BasicType, d: int) -> TypedNode:
    """ SE-Int """
    assert (isinstance(T, BasicType))

    value = round(random.gauss(0, 0.05) * 7500)
    t = T if ctx.inside_refinement else refine_literal(value, T, '_i')

    logging.info("se_int/{}: {}:{} ".format(d, value, t))
    return Literal(value, t)


def se_double(ctx: TypingContext, T: BasicType, d: int) -> TypedNode:
    """ SE-Double """
    assert (isinstance(T, BasicType))

    value = random.gauss(0, 0.05) * 7500
    t = T if ctx.inside_refinement else refine_literal(value, T, '_f')

    logging.info("se_double/{}: {}:{} ".format(d, value, t))
    return Literal(value, t)


def se_string(ctx: TypingContext, T: BasicType, d: int) -> TypedNode:
    """ SE-String """
    assert (isinstance(T, BasicType))

    length = max(1, round(abs(random.gauss(0, 1) * 10)))
    value = ''.join(random.choice(string.ascii_letters) for i in range(length))

    logging.info("se_string/{}: {}:{} ".format(d, value, T))

    # First refinement:
    if ctx.inside_refinement:
        typee = T
    else:
        typee = refine_literal(value, T, '_s')

    return Literal(value, typee)


def se_if(ctx: TypingContext, T: Type, d: int) -> TypedNode:
    """ SE-If """
    e1 = se(ctx, t_b, d - 1)
    e2 = se(ctx.with_cond(e1), T, d - 1)
    e3 = se(ctx.with_cond(Application(Var("!"), e1)), T, d - 1)
    logging.info("se_if/{}: if {} then {} else {} :{} ".format(
        d, e1, e2, e3, T))
    return If(e1, e2, e3).with_type(T)


def se_var(ctx: TypingContext, T: Type, d: int) -> TypedNode:
    """ SE-Var """
    options = get_variables_of_type(ctx, T)
    if options:
        n = random.choice(options)
        logging.info("se_var/{}: {}:{} ".format(d, n, T))
        return Var(n).with_type(T)
    raise Unsynthesizable("No var of type {}".format(T))


def se_abs(ctx: TypingContext, T: AbstractionType, d: int) -> TypedNode:
    """ SE-Abs """
    logging.info("se_abs/{}: {} ".format(d, T))
    nctx = ctx.with_var(T.arg_name, T.arg_type)
    body = se(nctx, T.return_type, d - 1)
    return Abstraction(T.arg_name, T.arg_type, body).with_type(T)


def se_app(ctx: TypingContext, T: Type, d: int) -> TypedNode:
    """ SE-App """
    logging.info("se_app/{}: {} ".format(d, T))
    k = sk(d - 1)
    U = st(ctx, k, d - 1)
    x = ctx.fresh_var()  #scfv(T)
    e2 = se(ctx, U, d - 1)

    nctx = ctx.with_var(x, U)
    V = iet(nctx, e2, x, T, d - 1)
    FT = AbstractionType(arg_name=x, arg_type=U, return_type=V)
    e1 = se(ctx, FT, d - 1)

    return Application(e1, e2).with_type(T)


def se_app_in_context(ctx: TypingContext, T: Type, d: int) -> TypedNode:
    logging.info("se_app_in_context/{}: {} ".format(d, T))

    refinement: Optional[TypedNode] = None
    if isinstance(T, RefinedType):
        target_type = T.type
        refinement = T.cond
    else:
        target_type = T

    options: List[Tuple[str, str, Type, Optional[str], Optional[Type],
                        Optional[TypedNode]]] = []
    for name in ctx.variables:
        t = ctx.variables[name]
        if isinstance(t, AbstractionType):
            ret = t.return_type
            if isinstance(ret, RefinedType):
                ret_refinement = ret.cond
                if tc.is_subtype(ctx, ret.type, target_type):
                    options.append((name, t.arg_name, t.arg_type, ret.name,
                                    ret.type, ret.cond))
            else:
                if tc.is_subtype(ctx, ret, target_type):
                    options.append(
                        (name, t.arg_name, t.arg_type, None, ret, None))

    if not options:
        raise Unsynthesizable("No function with that return type")

    (name, arg_name, arg_type, ret_name, retT,
     refinement) = random.choice(options)
    logging.info(
        "chosen name:{}, arg_name:{}, arg_type:{}, ret:{}, refine:{}".format(
            name, arg_name, arg_type, retT, refinement))
    if ret_name and refinement:
        ncond: TypedNode = refinement
        if isinstance(T, RefinedType):
            r2 = substitution_expr_in_expr(T.cond, Var(ret_name), T.name)
            ncond = Application(Application(Var("&&"), ncond), r2)
        logging.info("Requiring type: {}".format(
            RefinedType(arg_name, arg_type, ncond)))
        e2 = se_where(ctx.with_var(ret_name, retT),
                      RefinedType(arg_name, arg_type, ncond), d - 1)
    else:
        logging.info("Requiring only: {}".format(arg_type))
        e2 = se(ctx, arg_type, d - 1)
    e1 = Var(name)
    e = Application(e1, e2)
    if not tc.check_type(ctx, e, T):
        logging.info("se_app_in_context: failed restriction")
        raise Unsynthesizable("Failed restriction")
    return e


def se_where(ctx: TypingContext, T: RefinedType, d: int):
    """ SE-Where """
    logging.info("se_where/{}: {} ".format(d, T))

    if isinstance(T.type, RefinedType):
        T = flatten_refined_type(T)

    new_condition = filter_refinements(ctx, T.name, T.cond)

    if new_condition is None:
        e2 = se(ctx, T.type, d - 1)
    else:
        T.cond = new_condition
        try:
            e2 = try_ranged(ctx, T)
        except RangedException:
            e2 = se(ctx, T.type, d - 1)

    try:
        tc.check_type(ctx, e2, T)
        #if tc.entails(ctx.with_var(T.name, T).with_uninterpreted(), ncond):
        return e2  #.with_type(T)
    except:
        logging.info("se_where: failed restriction: {}", T)
        raise Unsynthesizable(
            "Unable to generate a refinement example: {}".format(T))


def se_tabs(ctx: TypingContext, T: TypeAbstraction, d: int):
    """ SE-TAbs """
    logging.info("se_tabs/{}: {} ".format(d, T))
    nctx = ctx.with_type_var(T.name, T.kind)
    e = se(nctx, T.type, d - 1)
    return TAbstraction(T.name, T.kind, e).with_type(T)


def se_tapp(ctx: TypingContext, T: Type, d: int):
    """ SE-TApp """
    logging.info("se_tapp/{}: {} ".format(d, T))
    k = sk(d - 1)
    U = st(ctx, k, d - 1)
    t = ctx.fresh_var()  #scfv(ctx, upper=True)
    V = itt(ctx.with_type_var(t, k), U, t, T, d - 1)
    e = se(ctx, TypeAbstraction(t, k, V), d - 1)
    return TApplication(e, U)


def se_subtype(ctx: TypingContext, T: Type, d: int):
    logging.info("se_subtype/{}: {} ".format(d, T))
    U = ssub(ctx, T, d - 1)
    return se(ctx, U, d - 1)


def has_applications_return(ctx, T: Type):
    for name, typee in ctx.variables.items():
        new_ctx = ctx.copy()
        while isinstance(typee, AbstractionType):
            new_ctx.add_var(typee.arg_name, typee.arg_type)
            if tc.is_subtype(new_ctx, typee, T) or tc.is_subtype(
                    new_ctx, T, typee.arg_type):  # TODO: CHECK
                return True
            typee = typee.return_type
    return False


@random_chooser
def se(ctx: TypingContext, T: Type, d: int):
    """ Γ ⸠ T~>_{d} e """

    if isinstance(T, BasicType) and T.name in ["Integer", "Top", "Object"]:
        yield ("se_int", se_int)
    if isinstance(T, BasicType) and T.name in ["Boolean", "Top", "Object"]:
        yield ("se_bool", se_bool)
    if isinstance(T, BasicType) and T.name in ["String", "Top", "Object"]:
        yield ("se_string", se_string)
    if isinstance(T, BasicType) and T.name in ["Double", "Top", "Object"]:
        yield ("se_double", se_double)
    if isinstance(T, RefinedType):
        yield ("se_where", se_where)

    if get_variables_of_type(ctx, T):
        yield ("se_var", se_var)
    if d > 0:
        yield ("se_if", se_if)
        if isinstance(T, AbstractionType):
            yield ("se_abs", se_abs)
        if isinstance(T, TypeAbstraction):
            yield ("se_tabs", se_tabs)
        yield ("se_tapp", se_tapp)
        yield ("se_app", se_app)
        yield ("se_subtype", se_subtype)

    if get_valid_genetics(ctx, T, d):
        yield ("se_genetics", se_genetics)


def se_safe(ctx: TypingContext, T: Type, d: int):
    try:
        return se(ctx, T, d)
    except TypeCheckingError:
        print("Se-safe in action...")
        # Try until we get one that works
        return se_safe(ctx, T, d)
    except Unsynthesizable:
        # print("Se-safe in action: it can't synthesize...")
        # Try until we get one that works
        return se_safe(ctx, T, d)


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


def iet_tapp(ctx: TypingContext, e: TypedNode, x: str, TA: TypeApplication,
             d: int):
    """ IET-app """
    T = TA.target
    U = TA.argument
    Tp = iet(ctx, e, x, T, d - 1)
    Up = iet(ctx, e, x, U, d - 1)
    return TypeApplication(Tp, Up)


def iet_tabs(ctx: TypingContext, e: TypedNode, x: str, TB: TypeAbstraction,
             d: int):
    """ IET-Tabs """
    t = TB.name
    k = TB.kind
    T = TB.type
    Tp = iet(ctx.with_type_var(t, k), e, x, T, d - 1)
    return TypeAbstraction(t, k, Tp)


@random_chooser
def iet(ctx: TypingContext, e: TypedNode, x: str, T: Type, d: int):
    """ Γ ⸠ [e/x] T ~>_{d} U """
    yield ("iet_id", iet_id)
    if isinstance(T, AbstractionType):
        yield ("iet_abs", iet_abs)
    if isinstance(T, TypeApplication):
        yield ("iet_tapp", iet_tapp)
    if isinstance(T, RefinedType):
        yield ("iet_where", iet_where)
    if isinstance(T, TypeAbstraction):
        yield ("iet_tabs", iet_tabs)


""" Inverse exp-subs in expression """


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
    e = tapp.target
    T = tapp.argument
    ep = iee(ctx, ex, x, e, d - 1)
    Tp = iet(ctx, ex, x, T, d - 1)
    return TApplication(ep, Tp)


def iee_tabs(ctx: TypingContext, ex: TypedNode, x: str, tapp: TAbstraction,
             d: int):
    """ IEE-TAbs """
    T = tapp.body
    Tp = iee(ctx, ex, x, T, d - 1)
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
    u = tapp.typevar
    k = tapp.kind
    U = tapp.body
    Up = itt(ctx.with_type_var(u, k), T, t, U, d - 1)
    return TAbstraction(u, k, Up)


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


def ssub_whereL(ctx: TypingContext, T: RefinedType, d: int) -> Type:
    """ SSub-whereL """
    U = ssub(ctx, T.type, d - 1)
    nctx = ctx.with_var(T.name, U)
    if tc.entails(nctx, T.cond):
        return U
    raise Unsynthesizable("Subtype where condition is not valid: {}".format(T))


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
def ssub(ctx: TypingContext, T: Type,
         d: int) -> Generator[Tuple[str, Any], None, None]:
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
    newCtx = ctx.with_var(x, T)
    e = se(newCtx, t_b, d - 1)
    if tc.entails(newCtx, e):
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
def ssup(ctx: TypingContext, T: Type,
         d: int) -> Generator[Tuple[str, Any], None, None]:
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


# =============================================================================
# ============================================= From Refinement to random value
# TODO: FORGOT LAMBDA EXPRESSIONS IN REFINEMENTS
def refined_random(variable, typee: Type, expression: TypedNode):

    # Transform the expression, so the variable is on the right side
    expression = transform_expression(variable, expression)

    max, min = get_max_min(expression)

    # Just for integers for now
    return random.randrange(min, max, 1)


def transform_expression(variable, expression):
    target = expression.target

    # Just in case it is the !
    if isinstance(target, Application):
        target = target.target

    if target.name in ['&&', '||', '-->']:
        expression.argument = transform_expression(variable,
                                                   expression.argument)
        expression.target.argument = transform_expression(
            variable, expression.target.argument)
    elif target.name in ['!']:
        expression.argument = transform_expression(variable,
                                                   expression.argument)
    elif target.name in ['>', '>=', '<', '<=', '==', '!=']:
        expression = invert_expression(variable, expression)
    else:
        # Invocation of functions
        pass

    return expression


def invert_expression(variable, expression):
    application = expression.target.target

    # x, 1 + 3 + x > 43
    while not isinstance(expression.target.argument,
                         Var) and expression.target.argument.name == variable:
        pass

    return expression
