from .ast import *
from .types import *
from .substitutions import *
from .zed import *


class TypeException(Exception):
    def __init__(self,
                 name,
                 description="",
                 given=None,
                 expected=None,
                 *args,
                 **kwargs):
        super(TypeException, self).__init__(name, description)
        self.expected = expected
        self.given = given


def sub_base(ctx, sub: BasicType, sup: BasicType):
    """ Sub-Int, Sub-Bool, Sub-Var """
    return sub.name == sup.name


def sub_whereL(ctx, sub: RefinedType, sup: Type):
    """ Sub-WhereL """
    nctx = ctx.with_var(sub.name, sub.type)
    return is_subtype(ctx, sub.type, sup) and \
        is_satisfiable(nctx, sub.cond)


def sub_whereR(ctx, sub: Type, sup: RefinedType):
    """ Sub-WhereR """
    nctx = ctx.with_var(sup.name, sub)
    return is_subtype(ctx, sub, sup.type) and \
        is_satisfiable(nctx, sup.cond)


def sub_arrow(ctx, sub: ArrowType, sup: ArrowType):
    """ Sub-Arrow """
    nctx = ctx.with_var(sup.arg_name, sup.arg_type)
    sub_return_type = substitution_var_in_type(sub.return_type, sup.arg_name,
                                               sub.arg_name)
    return is_subtype(ctx, sup.arg_type, sub.arg_type) and \
        is_subtype(nctx, sub_return_type, sup.return_type)


def sub_abs(ctx, sub: TypeAbstraction, sup: TypeAbstraction):
    """ Sub-Abs """
    if sub.kind != sup.kind:
        return False
    nctx = ctx.with_type_var(sup.name, sup.kind)
    return is_subtype(nctx,
                      substitution_type_in_type(sub.type, sup.name, sub.name),
                      sup.type)


def is_same_type(ctx, a, b):
    return is_subtype(ctx, a, b) and is_subtype(ctx, b, a)


def is_subtype(ctx, sub, sup):
    """ Subtyping Rules """
    print(sub, " <: ", sup)
    if type(sup) is BasicType:
        if sup.name in ['Void', 'Object']:
            return True  # Top
    if type(sub) is BasicType and type(sup) is BasicType:
        return sub_base(ctx, sub, sup)
    if type(sub) is RefinedType:
        return sub_whereL(ctx, sub, sup)
    if type(sup) is RefinedType:
        return sub_whereR(ctx, sub, sup)
    if type(sub) is ArrowType and type(sup) is ArrowType:
        return sub_arrow(ctx, sub, sup)
    if type(sub) is TypeAbstraction and type(sup) is TypeAbstraction:
        return sub_abs(ctx, sub, sup)

    raise Exception('No subtyping rule for {} <: {}'.format(sub, sup))


def extract_clauses(t):
    if type(t) is RefinedType:
        return [t.cond] + extract_clauses(t.type)
    return []


def expr_eval(ctx, t: RefinedType):
    conditions = extract_clauses(t)
    return is_satisfiable(conditions)


def is_satisfiable(ctx, cond):
    cond_type = tc(ctx, cond).type
    if not is_subtype(ctx, cond_type, t_b):
        raise TypeException(
            'Clause not boolean',
            "Condition {} is not a boolean expression".format(cond))
    else:
        return zed_verify_satisfiability(ctx, cond)


def wellformed(ctx, t):
    """ kind of type = wellformed(\Gamma, t) """
    if type(t) is BasicType:
        if ctx.is_basic_type(t):
            return star
        elif t.name in ctx.type_variables:
            return ctx.type_variables[t.name]
        else:
            raise TypeException('Unknown type',
                                "Type {} is not a known basic type".format(t))
    elif type(t) is ArrowType:

        k1 = wellformed(ctx, t.arg_type)
        k2 = wellformed(ctx.with_var(t.arg_name, t.arg_type), t.return_type)
        return k2
    elif type(t) is RefinedType:
        k = wellformed(ctx, t.type)
        if t.name in ctx.variables.keys():
            raise TypeException('Variable {} already in use.'.format(t.name),
                                "A new variable name should be defined")
        nctx = ctx.with_var(t.name, t.type)
        if not is_satisfiable(nctx, t.cond):
            raise TypeException(
                'Type is not satisfiable',
                "Type {} should be satisfiable in {}.".format(
                    t, ctx.variables))
        return star
    elif type(t) is TypeAbstraction:
        nctx = ctx.with_type_var(t.name, t.kind)
        k = wellformed(nctx, t.type)
        return Kind(t.kind, k)
    elif type(t) is TypeApplication:
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
    return e.type == t or (wellformed(ctx, e.type)
                           and is_subtype(ctx, e.type, t))


def e_literal(ctx, n, expects=None):
    """ E-Bool, E-Int, E-Basic """
    # Literals have their type filled
    return n


def e_var(ctx, n, expects=None):
    """ E-Var """
    if n.name not in ctx.variables:
        raise Exception(
            'Unknown variable',
            "Unknown variable {}.\n {}".format(n.name, ctx.variables))
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
                                                n.arg_name, expects.arg_name)
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
    if not type(n.target.type) is ArrowType:
        raise TypeException('Not a function',
                            "{} does not have the right type".format(n),
                            expects=expects,
                            given=n.target.type)

    ftype = n.target.type
    wellformed(ctx, ftype)
    n.argument = tc(ctx, n.argument, expects=ftype.arg_type)
    n.type = ftype.return_type
    return n


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


def tc(ctx, n, expects=None):
    """ TypeChecking AST nodes. Expects make it bidirectional """
    if type(n) is list:
        return [tc(ctx, e) for e in n]
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
    elif type(n) is Program:
        n = tc(ctx, n.declarations)
    elif type(n) is TypeDeclaration:
        ctx.add_type_var(n.name, n.kind)
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
