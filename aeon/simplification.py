from aeon.typechecker.substitutions import substitution_expr_in_expr
from typing import Callable, Tuple

from .ast import *
from .typechecker.ast_helpers import smt_eq, smt_true, is_unop, mk_unop, is_binop, binop_args, mk_binop, is_t_binop, t_binop_args, mk_t_binop, smt_and, smt_or, smt_not



def map_expr(f:Callable[[Any, TypedNode], Optional[TypedNode]], n:TypedNode) -> TypedNode:
    rec = lambda x: map_expr(f, x)
    nn = f(rec, n)
    if nn:
        return nn
    elif isinstance(n, Application):
        return Application(rec(n.target), rec(n.argument))
    elif isinstance(n, TApplication):
        return TApplication(rec(n.target), n.argument)
    elif isinstance(n, If):
        return If(rec(n.cond), rec(n.then), rec(n.otherwise))
    elif isinstance(n, Abstraction):
        return Abstraction(n.arg_name, n.arg_type, rec(n.body))
    elif isinstance(n, TAbstraction):
        return TAbstraction(n.type, n.kind, rec(n.body))
    return n

def to_nnf_helper(rec, n:TypedNode) -> Optional[TypedNode]:
    if is_binop(n, "-->"):
        (a, b) = binop_args(n)
        return rec(smt_or(smt_not(a), rec(b)))
    elif is_unop(n, "smtNot"):
        assert (isinstance(n, Application))
        if is_binop(n.argument, "smtAnd"):
            (a, b) = binop_args(n.argument)
            return smt_or(rec(smt_not(a)),
                          rec(smt_not(b)))
        elif is_binop(n.argument, "smtOr"):
            (a, b) = binop_args(n.argument)
            return smt_and(rec(smt_not(a)),
                           rec(smt_not(b)))
        else:
            return smt_not(rec(n.argument))
    return None

def to_nnf(n: TypedNode) -> TypedNode:
    return map_expr(to_nnf_helper, n)


def to_cnf_helper(rec, n:TypedNode) -> Optional[TypedNode]:
    if is_binop(n, "smtEq"):
        (a, b) = binop_args(n)
        (a, b) = (rec(a), rec(b))
        if a == b:
            return smt_true
        else:
            return smt_eq(a, b)
    elif is_binop(n, "smtAnd"):
        (a, b) = binop_args(n)
        (ap, bp) = (rec(a), rec(b))
        if is_binop(ap, "smtAnd"):
            (c, d) = binop_args(ap)
            return smt_and(c, smt_and(d, bp))
        return smt_and(ap, bp)
    elif is_binop(n, "smtOr"):
        assert (isinstance(n, Application))
        (a, b) = binop_args(n)
        if is_binop(a, "smtAnd"):
            assert (isinstance(a, Application))
            (c, d) = binop_args(a)
            na = mk_binop("smtOr", c, b)
            nb = mk_binop("smtOr", d, b)
            return rec(mk_binop("smtAnd", na, nb))
        if is_binop(b, "smtAnd"):
            assert (isinstance(b, Application))
            (c, d) = binop_args(b)
            na = mk_binop("smtOr", a, c)
            nb = mk_binop("smtOr", a, d)
            return rec(mk_binop("smtAnd", na, nb))
    return None

def to_cnf(n: TypedNode) -> TypedNode:
    return map_expr(to_cnf_helper, n)

def invert_comparisons_helper(rec, n:TypedNode) -> Optional[TypedNode]:
    if is_unop(n, "smtNot"):

        assert (isinstance(n, Application))
        if is_unop(n.argument, "smtNot"):
            assert (isinstance(n.argument, Application))
            return rec(n.argument.argument)

        opposites = [
            ('smtLte', 'smtGt'),
            ('smtGte', 'smtLt'),
            ('smtGt', 'smtLte'),
            ('smtLt', 'smtGte'),
            ('smtIneq', 'smtEq'),
            ('smtEq', 'smtIneq'),
        ]
        for (r, op) in opposites:
            if is_t_binop(n.argument, r):
                (a, b, t) = t_binop_args(n.argument)
                (a, b) = (rec(a), rec(b))
                return mk_t_binop(op, t, a, b)
            elif is_binop(n.argument, r):

                (a, b) = binop_args(n.argument)
                (a, b) = (rec(a), rec(b))
                return mk_binop(op, a, b)
    return None

def invert_comparisons(n: TypedNode) -> TypedNode:
    return map_expr(invert_comparisons_helper, n)


def remove_eqs_helper(n:TypedNode, forbidden_variables:List[str]) -> Optional[Tuple[str, TypedNode]]:
    if is_binop(n, "smtEq"):
        (c, d) = binop_args(n)
        if c == d:
            return None
        elif isinstance(c, Var) and c.name not in forbidden_variables:
            return (c.name,d)
        elif isinstance(d, Var) and d.name not in forbidden_variables:
            return (d.name, c)
    return None

def remove_eqs(n:TypedNode, forbidden_variables:List[str]) -> TypedNode:
    comp = n
    will_replace = None
    while is_binop(comp, "smtAnd"):
        (a, b) = binop_args(comp)
        will_replace = remove_eqs_helper(a, forbidden_variables)
        if will_replace:
            break
        comp = b
    if not will_replace:
        will_replace = remove_eqs_helper(comp, forbidden_variables)

    if will_replace:
        return remove_eqs(substitution_expr_in_expr(n, will_replace[1], will_replace[0]), forbidden_variables)
    return n

def cnf_simplify(n: TypedNode) -> TypedNode:
    n = to_nnf(n)
    n = to_cnf(n)
    n = invert_comparisons(n)
    return n


if __name__ == "__main__":
    from .frontend_core import expr
    x = expr.parse("((a < 1) --> ((b < 3) && (! ((c > 3) || (d > 3 ) ) )))")
    y = cnf_simplify(x)
    print(y)
