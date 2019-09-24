from .ast import *
from .types import *
from .substitutions import *
from .synthesis import *
from .zed import *


def sub_base(ctx, sub: BasicType, sup: BasicType):
    """ S-Int, S-Bool, S-Var """
    return sub.typeName == sup.typeName


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
    nctx = ctx.with_var(sup.name, sup.arg_type)
    sub_return_type = substitution_expr_in_type(sub.return_type,
                                                Var(sup.name),
                                                sub.name)
    return is_subtype(ctx, sup.arg_type, sub.arg_type) and \
        is_subtype(nctx, sub_return_type, sup.return_type)


def sub_tabs(ctx, sub: TypeAbstraction, sup: TypeAbstraction):
    """ S-TAbs """
    if sub.kind != sup.kind:
        return False
    nctx = ctx.with_type_var(sup.name, sup.kind)
    return is_subtype(
        nctx, substitution_type_in_type(sub.type, BasicType(sup.typeName),
                                        sub.typeName), sup.type)


def sub_tapp(ctx, sub: TypeApplication, sup: TypeApplication):
    """ S-TApp . Final case """
    if type(sub.target) is BasicType and type(sup.target) is BasicType:
        return sub.target.typeName == sup.target.typeName and is_subtype(
            ctx, sub.argument, sup.argument)
    print("Weird bug in sub_tapp", sub, sup)
    return False


def sub_appL(ctx, sub: TypeApplication, sup: TypeApplication):
    """ S-AppL . Beta-reduction on the left """
    abst = sub.target
    nsub = substitution_type_in_type(abst.type, abst.name, sub.argument)
    return is_subtype(ctx, nsub, sup)


def sub_appR(ctx, sub: TypeApplication, sup: TypeApplication):
    """ S-AppR . Beta-reduction on the right"""
    abst = sup.target
    nsup = substitution_type_in_type(abst.type, abst.name, sup.argument)
    return is_subtype(ctx, sub, nsup)


def is_same_type(ctx, a, b):
    return is_subtype(ctx, a, b) and is_subtype(ctx, b, a)


def is_subtype(ctx, sub, sup):
    """ Subtyping Rules """
    if type(sub) is BasicType:
        if sub.typeName == 'Bottom':
            return True  # Bottom
        if sub.typeName in ctx.type_aliases:
            return is_subtype(ctx, ctx.type_aliases[sub.typeName], sup)
    if type(sup) is BasicType:
        if sup.typeName in ['Void', 'Object']:
            return True  # Top
        if sup.typeName in ctx.type_aliases:
            return is_subtype(ctx, sub, ctx.type_aliases[sup.typeName])

    if type(sub) is BasicType:
        if sub.typeName in ['Void', 'Object']:
            return False  # Top
    if type(sup) is BasicType:
        if sup.typeName == 'Bottom':
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
    if type(sub) is TypeApplication and type(sup) is TypeApplication:
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
    return is_satisfiable(conditions)


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


def k_base(ctx, t):
    """ K-Int, K-Bool, K-Var """
    if ctx.is_basic_type(t):
        return star
    elif t.name in ctx.type_variables:
        return ctx.type_variables[t.name]
    elif t.name in ctx.type_aliases:
        return wellformed(ctx, ctx.type_aliases[t.name])
    else:
        raise TypeException('Unknown type',
                            "Type {} is not a known basic type".format(t))


def k_abs(ctx, t):
    """ K-Abs """
    k1 = wellformed(ctx, t.arg_type)  # TODO
    k2 = wellformed(ctx.with_var(t.arg_name, t.arg_type), t.return_type)
    return k2


def k_tabs(ctx, t):
    """ K-TAbs """
    nctx = ctx.with_type_var(t.name, t.kind)
    k = wellformed(nctx, t.type)
    return Kind(t.kind, k)


def k_tapp(ctx, t):
    """ K-TApp """
    k = wellformed(ctx, t.target)
    if k.is_star():
        raise TypeException(
            'Type application required a type abstraction',
            "Application {} requires an abstraction as function".format(t))
    ka = wellformed(ctx, t.argument)
    if ka != k.k1:
        raise TypeException('Kind does not match',
                            "Kind {} is not the same as {}".format(ka, k1))
    return k.k2


def k_where(ctx, t):
    """ K-Where """
    k = wellformed(ctx, t.type)

    if t.name in list(ctx.variables):
        return star
    nctx = ctx.with_var(t.name, t.type)
    t.cond = tc(nctx, t.cond, expects=t_b)
    if not is_satisfiable(nctx, t.cond):
        raise TypeException(
            'Type is not satisfiable',
            "Type {} should be satisfiable in {}.".format(t, ctx.variables))
    return star


def wellformed(ctx, t):
    """ Gamma |- T : k """
    if type(t) is BasicType:
        return k_base(ctx, t)
    elif type(t) is AbstractionType:
        return k_abs(ctx, t)
    elif type(t) is RefinedType:
        return k_where(ctx, t)
    elif type(t) is TypeAbstraction:
        return k_tabs(ctx, t)
    elif type(t) is TypeApplication:
        return k_tapp(ctx, t)
    raise Exception('No wellformed rule for {}'.format(t))


## HELPERS:


def check_expects(ctx, n, expects):
    if expects and not expr_has_type(ctx, n, expects):
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

    return wellformed(ctx, e.type) and is_subtype(ctx, e.type, t)


def e_literal(ctx, n, expects=None):
    """ E-Bool, E-Int, E-Basic """
    # Literals have their type filled
    if not n.type:
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
                                 Literal(value=n.value, type=btype)))

    return n


def e_var(ctx, n, expects=None):
    """ E-Var """
    if n.name not in list(ctx.variables):
        raise Exception(
            'Unknown variable',
            "Unknown variable {}.\n {}".format(n.name, list(ctx.variables)))
    n.type = ctx.variables[n.name]
    return n


def e_if(ctx, n, expects=None):
    """ E-If """
    n.cond = tc(ctx, n.cond, expects=t_b)
    n.then = tc(ctx, n.then, expects=expects)  # TODO: Missing context clauses
    n.otherwise = tc(ctx, n.otherwise, expects=expects)  # TODO: same
    if expects:
        n.type = expects
    else:
        n.type = n.then.type  # TODO - missing least common supertype else
    return n


def e_abs(ctx, n, expects=None):
    """ E-Abs """
    if expects and type(expects) is AbstractionType:
        body_expects = substitution_expr_in_type(expects.return_type,
                                                 Var(n.name),
                                                 expects.name)
    else:
        body_expects = None
    nctx = ctx.with_var(n.name, n.arg_type)
    n.body = tc(nctx, n.body, expects=body_expects)
    n.type = AbstractionType(name=n.name,
                             arg_type=n.arg_type,
                             return_type=n.body.type)
    return n


def e_app(ctx, n, expects=None):
    """ E-App """
    n.target = tc(ctx, n.target, expects=None)

    if "+" in str(n):
        print("Target:", n.target, n.target.type)
        print("Argument", n.target, n.target.type)

    if type(n.target.type) is AbstractionType:
        ftype = n.target.type
        nctx = ctx.with_var(n.target.type.name, n.target.type.arg_type)
        wellformed(nctx, ftype)
        n.argument = tc(ctx, n.argument, expects=ftype.arg_type)
        n.type = substitution_expr_in_type(ftype.return_type, n.argument,
                                           n.target.type.name)

        return n
    else:
        raise TypeException(
            'Not a function',
            "{} does not have the right type (had {}, expected {})".format(
                n, n.target.type, expects),
            expects=expects,
            given=n.target.type)


def e_tapp(ctx, n, expects=None):
    """ E-TApp """
    n.target = tc(ctx, n.target, expects=None)
    if not type(n.target.type) is TypeAbstraction:
        raise TypeException('Not a type function',
                            "{} does not have the right type".format(n),
                            expects=expects,
                            given=n.target.type)

    tabs = n.target.type

    k1 = wellformed(ctx, tabs)
    k2 = wellformed(ctx, n.argument)
    if k1 != k2:
        raise TypeException('Type abstraction has wrong kind',
                            "In Type Application".format(n),
                            expects=k2,
                            given=k1)

    n.type = substitution_type_in_type(tabs.type, n.argument, tabs.name)
    return n


def e_tabs(ctx, n, expects=None):
    """ E-TAbs """
    a_expects = None
    if expects and type(expects) is TypeAbstraction:
        a_expects = expects.type
    nctx = ctx.with_type_var(n.typevar, n.kind)
    n.body = tc(nctx, n.body, a_expects)
    n.type = TypeAbstraction(name=n.typevar, kind=n.kind, type=n.body.type)
    return n


def tc(ctx, n, expects=None):
    """ TypeChecking AST nodes. Expects make it bidirectional """
    if type(n) is list:
        return [tc(ctx, e) for e in n]
    elif type(n) is Hole:
        n = synthesize(ctx, n.type)
    elif type(n) is Literal:
        n = e_literal(ctx, n, expects)
    elif type(n) is Var:
        n = e_var(ctx, n, expects)
    elif type(n) is If:
        n = e_if(ctx, n, expects)
    elif type(n) is Application:
        n = e_app(ctx, n, expects)
    elif type(n) is Abstraction:
        n = e_abs(ctx, n, expects)
    elif type(n) is TApplication:
        n = e_tapp(ctx, n, expects)
    elif type(n) is TAbstraction:
        n = e_tabs(ctx, n, expects)
    elif type(n) is Program:
        n.declarations = tc(ctx, n.declarations)
    elif type(n) is TypeDeclaration:
        ctx.add_type_var(n.name, n.kind)
    elif type(n) is TypeAlias:
        ctx.type_aliases[n.name] = n.type
    elif type(n) is Definition:
        k = wellformed(ctx, n.type)
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
