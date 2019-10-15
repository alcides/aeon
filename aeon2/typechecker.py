from .ast import Var, TAbstraction, TApplication, Application, Abstraction, Literal
from .types import Type, BasicType, RefinedType, AbstractionType, TypeAbstraction, \
    TypeApplication, Kind, AnyKind, star, TypeException, t_b
from .substitutions import substitution_expr_in_type, substitution_type_in_type, \
    substitution_expr_in_expr, substitution_type_in_expr
from .synthesis import *
from .zed import zed_verify_entailment, zed_verify_satisfiability, NotDecidableException

# TODO: factorial. kinding is not correct.


def sub_base(ctx, sub: BasicType, sup: BasicType):
    """ S-Int, S-Bool, S-Var """
    return sub.name == sup.name


def sub_whereL(ctx, sub: RefinedType, sup: Type):
    """ S-WhereL """
    nctx = ctx.with_var(sub.name, sub.type)
    return is_satisfiable(nctx, sub.cond) and \
        is_subtype(ctx, sub.type, sup)


def sub_whereR(ctx, sub: Type, sup: RefinedType):
    """ S-WhereR """
    nctx = ctx.with_var(sup.name, sub)
    return is_subtype(ctx, sub, sup.type) and \
        entails(nctx, sup.cond)


def sub_abs(ctx, sub: AbstractionType, sup: AbstractionType):
    """ S-Abs """
    nctx = ctx.with_var(sup.arg_name, sup.arg_type)
    sub_return_type = substitution_expr_in_type(sub.return_type,
                                                Var(sup.arg_name),
                                                sub.arg_name)
    return is_subtype(ctx, sup.arg_type, sub.arg_type) and \
        is_subtype(nctx, sub_return_type, sup.return_type)


def sub_tabs(ctx, sub: TypeAbstraction, sup: TypeAbstraction):
    """ S-TAbs """
    if sub.kind != sup.kind:
        return False
    nctx = ctx.with_type_var(sup.name, sup.kind)
    return is_subtype(
        nctx, substitution_type_in_type(sub.type, BasicType(sup.name),
                                        sub.name), sup.type)


def sub_tapp(ctx, sub: TypeApplication, sup: TypeApplication):
    """ S-TApp . Final case """
    if type(sub.target) is BasicType and type(sup.target) is BasicType:
        return sub.target.name == sup.target.name and is_subtype(
            ctx, sub.argument, sup.argument)
    print("Weird bug in sub_tapp", sub, sup)
    return False


def sub_appL(ctx, sub: TypeApplication, sup: Type):
    """ S-Cong + C-Beta on the left """
    abst = sub.target
    assert (type(sub.target) == TypeAbstraction)
    nsub = substitution_type_in_type(abst.type, sub.argument, abst.name)
    return is_subtype(ctx, nsub, sup)


def sub_appR(ctx, sub: Type, sup: TypeApplication):
    """ S-Cong . C-Beta on the right"""
    abst = sup.target
    nsup = substitution_type_in_type(abst.type, sup.argument, abst.name)
    return is_subtype(ctx, sub, nsup)


def is_same_type(ctx, a, b):
    return is_subtype(ctx, a, b) and is_subtype(ctx, b, a)


def is_subtype(ctx, sub, sup):
    """ Subtyping Rules """
    if type(sub) is BasicType:
        if sub.name == 'Bottom':
            return True  # Bottom
        if sub.name in ctx.type_aliases:
            return is_subtype(ctx, ctx.type_aliases[sub.typeName], sup)
    if type(sup) is BasicType:
        if sup.name in ['Void', 'Object']:
            return True  # Top
        if sup.name in ctx.type_aliases:
            return is_subtype(ctx, sub, ctx.type_aliases[sup.typeName])

    if type(sub) is BasicType:
        if sub.name in ['Void', 'Object']:
            return False  # Top
    if type(sup) is BasicType:
        if sup.name == 'Bottom':
            return False  # Bottom

    if type(sub) is BasicType and type(sup) is BasicType:
        return sub_base(ctx, sub, sup)
    if type(sup) is RefinedType:
        return sub_whereR(ctx, sub, sup)
    if type(sub) is RefinedType:
        return sub_whereL(ctx, sub, sup)
    if type(sub) is AbstractionType and type(sup) is AbstractionType:
        return sub_abs(ctx, sub, sup)
    if type(sub) is TypeAbstraction and type(sup) is TypeAbstraction:
        return sub_tabs(ctx, sub, sup)
    if type(sub) is TypeApplication or type(sup) is TypeApplication:
        if type(sub.target) is TypeAbstraction:
            return sub_appL(ctx, sub, sup)
        if type(sup.target) is TypeAbstraction:
            return sub_appR(ctx, sub, sup)
        return sub_tapp(ctx, sub, sup)
    return False
    raise Exception('No subtyping rule for {} <: {}'.format(sub, sup))


def extract_clauses(t):
    if type(t) is RefinedType:
        return [t.cond] + extract_clauses(t.type)
    return []


def expr_eval(ctx, t: RefinedType):
    conditions = extract_clauses(t)
    return is_satisfiable(ctx, conditions)


def entails(ctx, cond):
    cond_type = tc(ctx, cond).type
    if not is_subtype(ctx, cond_type, t_b):
        raise TypeException(
            'Clause not boolean',
            "Condition {} is not a boolean expression".format(cond))
    else:
        return zed_verify_entailment(ctx, cond)


def is_satisfiable(ctx, cond):
    #cond_type = tc(ctx, cond).type
    if False:  #not is_subtype(ctx, cond_type, t_b):
        raise TypeException(
            'Clause not boolean',
            "Condition {} is not a boolean expression".format(cond))
    else:
        try:
            cond = tc(ctx, cond)
            return zed_verify_satisfiability(ctx, cond)
        except NotDecidableException:
            return True


def k_base(ctx, t, k: Kind):
    """ K-Int, K-Bool and K-Var """
    if t in ctx.type_variables:
        expected_kind = ctx.type_variables[t]
        if k != expected_kind:
            raise TypeException(
                "Wrong kinding",
                "{} has kind *. {} given instead.".format(t, k))
    else:
        raise TypeException("Unknown type {} of kind {}".format(t, k))
    return expected_kind


def k_abs(ctx, t: AbstractionType, k: Kind):
    """ K-Abs """
    x = t.arg_name
    T = t.arg_type
    U = t.return_type
    kinding(ctx, T, star)
    kinding(ctx.with_var(x, T), U, star)
    if not type(k) is AnyKind and k != star:
        raise TypeException("Type has wrong kinding.",
                            "Expected {}, given {}.".format(star, t))
    return star


def k_where(ctx, t: RefinedType, k: Kind):
    """ K-Where """
    t.cond = tc(ctx.with_var(t.name, t.type), t.cond, expects=t_b)
    return kinding(ctx, t.type, k)


def k_tabs(ctx, t: TypeAbstraction, k: Kind):
    """ K-TAbs """
    if type(k) != AnyKind:
        if k == star:
            raise TypeException("Type Abstraction cannot be of Kind *")

        if t.kind != k.k1:
            raise TypeException(
                "Argument of TypeAbstraction {} is not {}.".format(
                    t.kind, k.k1))

        k2 = kinding(ctx.with_type_var(BasicType(t.name), t.kind), t.type,
                     k.k2)
        if k2 != k.k2:
            raise TypeException(
                "Body of TypeAbstraction {} (kind: {}) is not of kind {}.".
                format(t, k2, k.k2))
    else:
        k2 = kinding(ctx.with_type_var(BasicType(t.name), t.kind), t.type, k)

    return Kind(k1=t.kind, k2=k2)


def k_tapp(ctx, t: TypeApplication, k: Kind):
    """ K-TApp """
    T = t.target
    U = t.argument
    k1 = kinding(ctx, U, AnyKind())
    k_a = kinding(ctx, T, Kind(k1=k1, k2=AnyKind()))
    if k != k_a.k2:
        raise TypeException(
            "Type Abstraction has wrong kinding.\nExpected {}, given {}.".
            format(k, k_a.k2))
    return k_a.k2


def kinding(ctx, t: Type, k: Kind):
    if type(t) is BasicType:
        return k_base(ctx, t, k)
    elif type(t) is AbstractionType:
        return k_abs(ctx, t, k)
    elif type(t) is RefinedType:
        return k_where(ctx, t, k)
    elif type(t) is TypeAbstraction:
        return k_tabs(ctx, t, k)
    elif type(t) is TypeApplication:
        return k_tapp(ctx, t, k)
    raise Exception('No kinding rule for {}'.format(t))


## HELPERS:


def check_expects(ctx, n, expects):
    if expects and not hasattr(n, "type"):  #  expr_has_type(ctx, n, expects):
        raise TypeException(
            '{} has wrong type'.format(type(n)),
            "{} has wrong type (given: {}, expected: {})".format(
                n, n.type, expects),
            expected=expects,
            given=n.type)


# Expression TypeChecking


def expr_has_type(ctx, e, t):
    """ E-Subtype """
    if not hasattr(e, "type") or e.type == None:
        tc(ctx, e, expects=t)
    if e.type == t:
        return True

    if type(t) is RefinedType:
        """ T-Where """
        ne = substitution_expr_in_expr(t.cond, e, t.name)
        return expr_has_type(ctx, e, t.type) and entails(ctx, ne)

    return kinding(ctx, e.type, AnyKind()) and is_subtype(ctx, e.type, t)


def t_literal(ctx, n, expects=None):
    """ T-Bool, T-Int, T-Basic """
    # Literals have their type filled
    if not n.type and not n.ensured:
        name = "Literal_{}".format(n.value)
        if type(n.value) == bool:
            btype = t_b
            op = "==="
        else:
            btype = t_i
            op = "=="
        n.type = RefinedType(name=name,
                             type=btype,
                             cond=Application(
                                 Application(Var(op), Var(name)),
                                 Literal(value=n.value,
                                         type=btype,
                                         ensured=True)))

    return n


def t_var(ctx, n, expects=None):
    """ T-Var """
    if n.name not in list(ctx.variables):
        raise Exception(
            'Unknown variable',
            "Unknown variable {}.\n {}".format(n.name, list(ctx.variables)))
    n.type = ctx.variables[n.name]
    return n


def t_if(ctx, n, expects=None):
    """ T-If """
    n.cond = tc(ctx, n.cond, expects=t_b)
    n.then = tc(ctx, n.then, expects=expects)  # TODO: Missing context clauses
    n.otherwise = tc(ctx, n.otherwise, expects=expects)  # TODO: same
    if expects:
        n.type = expects
    else:
        n.type = n.then.type  # TODO - missing least common supertype else
    return n


def t_abs(ctx, n, expects=None):
    """ T-Abs """
    if expects and type(expects) is AbstractionType:
        body_expects = substitution_expr_in_type(expects.return_type,
                                                 Var(n.arg_name),
                                                 expects.arg_name)
    else:
        body_expects = None
    nctx = ctx.with_var(n.arg_name, n.arg_type)
    n.body = tc(nctx, n.body, expects=body_expects)
    n.type = AbstractionType(arg_name=n.arg_name,
                             arg_type=n.arg_type,
                             return_type=n.body.type)
    return n


def t_app(ctx, n: Application, expects=None):
    """ T-App """
    n.target = tc(ctx, n.target, expects=None)

    if type(n.target.type) is AbstractionType:
        ftype = n.target.type
        nctx = ctx.with_var(n.target.type.arg_name, n.target.type.arg_type)
        n.argument = tc(ctx, n.argument, expects=ftype.arg_type)
        n.type = substitution_expr_in_type(ftype.return_type, n.argument,
                                           n.target.type.arg_name)
        return n
    else:
        raise TypeException(
            'Not a function',
            "{} does not have the right type (had {}, expected {})".format(
                n, n.target.type, expects),
            expects=expects,
            given=n.target.type)


def t_tabs(ctx, n: TAbstraction, expects: Type = None):
    """ E-TAbs """
    a_expects = None
    if expects and type(expects) is TypeAbstraction:
        a_expects = expects.type
    nctx = ctx.with_type_var(n.typevar, n.kind)
    n.body = tc(nctx, n.body, a_expects)
    n.type = TypeAbstraction(name=n.typevar, kind=n.kind, type=n.body.type)
    return n


def e_tapp(ctx, n: TAbstraction, expects=None):
    """ E-TApp """
    n.target = tc(ctx, n.target, expects=None)
    if not type(n.target.type) is TypeAbstraction:
        raise TypeException('Not a type function',
                            "{} does not have the right type".format(n),
                            expects=expects,
                            given=n.target.type)

    tabs = n.target.type

    kind_of_arg = kinding(ctx, n.argument, AnyKind())
    if tabs.kind != kind_of_arg:

        raise TypeException(
            "Type abstraction has wrong kind.\nIn Type Application {}.".format(
                n),
            expects=kind_of_arg,
            given=n.kind)

    n.type = substitution_type_in_type(tabs.type, n.argument, tabs.name)
    return n


def tc(ctx, n, expects=None):
    """ TypeChecking AST nodes. Expects make it bidirectional """
    if type(n) is list:
        return [tc(ctx, e) for e in n]
    elif type(n) is Hole:
        n = synthesize(ctx, n.type)
    elif type(n) is Literal:
        n = t_literal(ctx, n, expects)
    elif type(n) is Var:
        n = t_var(ctx, n, expects)
    elif type(n) is If:
        n = t_if(ctx, n, expects)
    elif type(n) is Application:
        n = t_app(ctx, n, expects)
    elif type(n) is Abstraction:
        n = t_abs(ctx, n, expects)
    elif type(n) is TApplication:
        n = e_tapp(ctx, n, expects)
    elif type(n) is TAbstraction:
        n = t_tabs(ctx, n, expects)
    elif type(n) is Program:
        n.declarations = tc(ctx, n.declarations)
    elif type(n) is TypeDeclaration:
        ctx.add_type_var(n.name, n.kind)
    elif type(n) is TypeAlias:
        ctx.type_aliases[n.name] = n.type
    elif type(n) is Definition:
        k = kinding(ctx, n.type, AnyKind())
        name = n.name
        body = n.body
        n.body = tc(ctx, body, expects=n.type)
        ctx.add_var(name, n.type)
        return n
    else:
        print("Could not typecheck {} of type {}".format(n, type(n)))
    check_expects(ctx, n, expects)
    return n


def typecheck(ast, refined=True, synthesiser=None):
    ctx = TypingContext()
    ctx.setup()
    return tc(ctx, ast), ctx, None


def synthesize(ctx, t):
    d = 1
    print(", ".join(list(ctx.variables.keys())), "|-", t, " ~> _", 3)
    n = se(ctx, t, 3)
    print(20 * "-")
    n = tc(ctx, n, t)
    print(n, ":", n.type)
    return n
