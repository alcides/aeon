from .typestructure import *


class TypeException(Exception):
    def __init__(self,
                 name,
                 description="",
                 given=None,
                 expected=None,
                 *args,
                 **kwargs):
        super(TypeException, self).__init__(name, description, *args, **kwargs)
        self.expected = expected
        self.given = given


def sub_base(ctx, sub: BasicType, sup: BasicType):
    """ Sub-Int, Sub-Bool, Sub-Var """
    return sub.name == sup.name


def is_subtype(ctx, sub, sup):
    """ Subtyping Rules """
    if type(sup) is BasicType:
        if sup.name in ['Void', 'Object']:
            return True  # Top
    if type(sub) is BasicType and type(sup) is BasicType:
        return sub_base(ctx, sub, sup)

    if type(sup) is BasicType:
        if sup.name in ['Void', 'Object']:  # Top
            return True
    print("Sup:", sup)
    return False  # TODO


def is_satisfiable(ctx, cond):
    cond_type = tc(ctx, cond).type
    if not is_subtype(ctx, cond_type, t_b):
        raise TypeException(
            'Clause not boolean',
            "Condition {} is not a boolean expression".format(t))
    else:
        print("TODO: Z3")
        return True


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
        k1 = wellformed(ctx, t.type)
        k2 = wellformed(ctx.with_var(t.argument, t.type), t.argument)
        return k2
    elif type(t) is RefinedType:
        t1 = wellformed(ctx, t.type)
        nctx = ctx.with_var(t.name, t.type)
        if not is_satisfiable(nctx, t.cond):
            raise TypeException('Type is not satisfiable',
                                "Type {} should be satisfiable.".format(t))
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
    print("No wellformed rule for ", t, type(t))
    return False


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
        raise TypeException(
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
