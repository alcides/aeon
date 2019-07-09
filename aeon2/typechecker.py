from .ast import *
from .types import *
from .substitutions import *
from .synthesis import *
from .zed import *


def sub_base(ctx, sub: BasicType, sup: BasicType):
    """ Sub-Int, Sub-Bool, Sub-Var """
    return sub.name == sup.name


def sub_whereL(ctx, sub: RefinedType, sup: Type):
    """ Sub-WhereL """
    nctx = ctx.with_var(sub.name, sub.type)
    return is_satisfiable(nctx, sub.cond) and \
        is_subtype(ctx, sub.type, sup)


def sub_whereR(ctx, sub: Type, sup: RefinedType):
    """ Sub-WhereR """
    nctx = ctx.with_var(sup.name, sub)
    return is_subtype(ctx, sub, sup.type) and \
        entails(nctx, sup.cond)


def sub_arrow(ctx, sub: ArrowType, sup: ArrowType):
    """ Sub-Arrow """
    nctx = ctx.with_var(sup.arg_name, sup.arg_type)
    sub_return_type = substitution_var_in_type(sub.return_type,
                                               Var(sup.arg_name), sub.arg_name)
    return is_subtype(ctx, sup.arg_type, sub.arg_type) and \
        is_subtype(nctx, sub_return_type, sup.return_type)


def sub_abs(ctx, sub: TypeAbstraction, sup: TypeAbstraction):
    """ Sub-Abs """
    if sub.kind != sup.kind:
        return False
    nctx = ctx.with_type_var(sup.name, sup.kind)
    return is_subtype(
        nctx, substitution_type_in_type(sub.type, BasicType(sup.name),
                                        sub.name), sup.type)


def sub_appT(ctx, sub: TypeApplication, sup: TypeApplication):
    """ Sub-AppT . Final case """
    if type(sub.target) is BasicType and type(sup.target) is BasicType:
        return sub.target.name == sup.target.name and is_subtype(
            ctx, sub.argument, sup.argument)
    print("Weird bug in sub_appT", sub, sup)
    return False


def sub_appL(ctx, sub: TypeApplication, sup: TypeApplication):
    """ Sub-AppL . Beta-reduction on the left """
    abst = sub.target
    nsub = substitution_type_in_type(abst.type, abst.name, sub.argument)
    return is_subtype(ctx, nsub, sup)


def sub_appR(ctx, sub: TypeApplication, sup: TypeApplication):
    """ Sub-AppR . Beta-reduction on the right"""
    abst = sup.target
    nsup = substitution_type_in_type(abst.type, abst.name, sup.argument)
    return is_subtype(ctx, sub, nsup)


def is_same_type(ctx, a, b):
    return is_subtype(ctx, a, b) and is_subtype(ctx, b, a)


def is_subtype(ctx, sub, sup):
    """ Subtyping Rules """
    if type(sub) is BasicType:
        if sub.name == 'Bottom':
            return True  # Bottom
        if sub.name in ctx.type_aliases:
            return is_subtype(ctx, ctx.type_aliases[sub.name], sup)
    if type(sup) is BasicType:
        if sup.name in ['Void', 'Object']:
            return True  # Top
        if sup.name in ctx.type_aliases:
            return is_subtype(ctx, sub, ctx.type_aliases[sup.name])

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
    if type(sub) is ArrowType and type(sup) is ArrowType:
        return sub_arrow(ctx, sub, sup)
    if type(sub) is TypeAbstraction and type(sup) is TypeAbstraction:
        return sub_abs(ctx, sub, sup)
    if type(sub) is TypeApplication and type(sup) is TypeApplication:
        if type(sub.target) is TypeAbstraction:
            return sub_appL(ctx, sub, sup)
        if type(sup.target) is TypeAbstraction:
            return sub_appR(ctx, sub, sup)
        return sub_appT(ctx, sub, sup)
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
            return zed_verify_satisfiability(ctx, cond)
        except NotDecidableException:
            return True


def t_base(ctx, t):
    """ T-Int, T-Bool, T-Cont """
    if ctx.is_basic_type(t):
        return star
    elif t.name in ctx.type_variables:
        return ctx.type_variables[t.name]
    elif t.name in ctx.type_aliases:
        return wellformed(ctx, ctx.type_aliases[t.name])
    else:
        raise TypeException('Unknown type',
                            "Type {} is not a known basic type".format(t))


def t_arrow(ctx, t):
    """ T-Arrow """
    k1 = wellformed(ctx, t.arg_type)  # TODO
    k2 = wellformed(ctx.with_var(t.arg_name, t.arg_type), t.return_type)
    return k2


def t_abs(ctx, t):
    """ T-Abs """
    nctx = ctx.with_type_var(t.name, t.kind)
    k = wellformed(nctx, t.type)
    return Kind(t.kind, k)


def t_app(ctx, t):
    """ T-App """
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


def t_where(ctx, t):
    """ T-Where """
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
    """ k = wellformed(\Gamma, T) """
    if type(t) is BasicType:
        return t_base(ctx, t)
    elif type(t) is ArrowType:
        return t_arrow(ctx, t)
    elif type(t) is RefinedType:
        return t_where(ctx, t)
    elif type(t) is TypeAbstraction:
        return t_abs(ctx, t)
    elif type(t) is TypeApplication:
        return t_app(ctx, t)
    raise Exception('No wellformed rule for {}'.format(t))


## HELPERS:


def check_expects(ctx, n, expects):
    if expects and not expr_has_type(ctx, n, expects):
        raise TypeException('{} has wrong type'.format(type(n)),
                            "{} has wrong type:".format(n),
                            expected=expects,
                            given=n.type)


# Expression TypeChecking


def expr_has_type(ctx, e, t):
    """ E-Subtype """
    if not hasattr(e, "type"):
        tc(ctx, e, expects=t)
    if e.type == t:
        return True

    if type(t) is RefinedType:
        """ T-Where """
        ne = substitution_in_expr(t.cond, e, t.name)
        return expr_has_type(ctx, e, t.type) and entails(ctx, ne)

    return wellformed(ctx, e.type) and is_subtype(ctx, e.type, t)


def e_literal(ctx, n, expects=None):
    """ E-Bool, E-Int, E-Basic """
    # Literals have their type filled
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
    n.type = expects
    return n


def e_abs(ctx, n, expects=None):
    """ E-Abs """
    if expects and type(expects) is ArrowType:
        body_expects = substitution_var_in_type(expects.return_type,
                                                Var(n.arg_name),
                                                expects.arg_name)
    else:
        body_expects = None
    nctx = ctx.with_var(n.arg_name, n.arg_type)
    n.body = tc(nctx, n.body, expects=body_expects)
    n.type = ArrowType(arg_name=n.arg_name,
                       arg_type=n.arg_type,
                       return_type=n.body.type)
    return n


def e_app(ctx, n, expects=None):
    """ E-App """
    n.target = tc(ctx, n.target, expects=None)
    if type(n.target.type) is ArrowType:
        ftype = n.target.type
        nctx = ctx.with_var(n.target.type.arg_name, n.target.type.arg_type)
        wellformed(nctx, ftype)
        n.argument = tc(ctx, n.argument, expects=ftype.arg_type)
        n.type = substitution_var_in_type(ftype.return_type, n.argument,
                                          n.target.type.arg_name)
        return n
    else:
        raise TypeException('Not a function',
                            "{} does not have the right type".format(n),
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
        tc(ctx, body, expects=n.type)
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
    d = 3
    print(", ".join(list(ctx.variables.keys())), "|-", t, " ~> _", 3)
    n = se(ctx, t, 3)
    n = tc(ctx, n, t)
    print(n, ":", n.type)
    return n
