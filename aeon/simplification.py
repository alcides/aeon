from typing import Tuple

from .ast import *


def is_unop(a: TypedNode, name: str = "") -> bool:
    return isinstance(a, Application) and isinstance(
        a.target, Var) and (name != "" and a.target.name == name)


def mk_unop(t: str, a: TypedNode):
    return Application(Var(t), a)


def is_binop(a: TypedNode, name: str = "") -> bool:
    return isinstance(
        a, Application) and isinstance(a.target, Application) and isinstance(
            a.target.target, Var) and (name != ""
                                       and a.target.target.name == name)


def binop_args(a: TypedNode) -> Tuple[TypedNode, TypedNode]:
    assert (isinstance(a, Application) and isinstance(a.target, Application))
    return (a.target.argument, a.argument)


def mk_binop(t: str, a: TypedNode, b: TypedNode):
    return Application(Application(Var(t), a), b)


def is_t_binop(a: TypedNode, name: str = "") -> bool:
    return isinstance(
        a, Application) and isinstance(a.target, Application) and isinstance(
            a.target.target, TApplication) and isinstance(
                a.target.target.target,
                Var) and (name != "" and a.target.target.target.name == name)


def t_binop_args(a: TypedNode) -> Tuple[TypedNode, TypedNode, Type]:
    assert (isinstance(a, Application) and isinstance(a.target, Application)
            and isinstance(a.target.target, TApplication)
            and isinstance(a.target.target.target, Var))
    return (a.target.argument, a.argument, a.target.target.argument)


def mk_t_binop(name: str, t: Type, a: TypedNode, b: TypedNode):
    return Application(Application(TApplication(Var(name), t), a), b)


def to_nnf(n: TypedNode) -> TypedNode:
    if is_binop(n, "-->"):
        (a, b) = binop_args(n)
        return to_nnf(mk_binop("||", mk_unop("!", a), b))
    elif is_unop(n, "!"):
        assert (isinstance(n, Application))
        if is_binop(n.argument, "&&"):
            (a, b) = binop_args(n.argument)
            return cnf_simplify(
                mk_binop("||", to_nnf(mk_unop("!", a)), to_nnf(mk_unop("!",
                                                                       b))))
        elif is_binop(n.argument, "||"):
            (a, b) = binop_args(n.argument)
            return mk_binop("&&", to_nnf(mk_unop("!", a)),
                            to_nnf(mk_unop("!", b)))
    elif isinstance(n, Application):
        return Application(to_nnf(n.target), to_nnf(n.argument))
    if isinstance(n, TApplication):
        return TApplication(to_nnf(n.target), n.argument)
    return n


def to_cnf(n: TypedNode) -> TypedNode:
    n = to_nnf(n)
    if is_binop(n, "||"):
        assert (isinstance(n, Application))
        (a, b) = binop_args(n)
        if is_binop(a, "&&"):
            assert (isinstance(a, Application))
            (c, d) = binop_args(a)
            na = mk_binop("||", c, b)
            nb = mk_binop("||", d, b)
            return to_cnf(mk_binop("&&", na, nb))
        if is_binop(b, "&&"):
            assert (isinstance(b, Application))
            (c, d) = binop_args(b)
            na = mk_binop("||", a, c)
            nb = mk_binop("||", a, d)
            return to_cnf(mk_binop("&&", na, nb))
    if isinstance(n, Application):
        return Application(to_cnf(n.target), to_cnf(n.argument))
    if isinstance(n, TApplication):
        return TApplication(to_cnf(n.target), n.argument)
    return n


def cnf_simplify(n: TypedNode) -> TypedNode:
    n = to_cnf(n)
    if is_unop(n, "!"):
        assert (isinstance(n, Application))
        if is_unop(n.argument, "!"):
            assert (isinstance(n.argument, Application))
            return cnf_simplify(n.argument.argument)

        opposites = [
            ('<=', '>'),
            ('>=', '<'),
            ('>', '<='),
            ('<', '>='),
            ('!=', '=='),
            ('==', '!='),
        ]
        for (r, op) in opposites:
            if is_t_binop(n.argument, r):
                (a, b, t) = t_binop_args(n.argument)
                return mk_t_binop(op, t, a, b)

    if isinstance(n, Application):
        return Application(cnf_simplify(n.target), cnf_simplify(n.argument))
    if isinstance(n, TApplication):
        return TApplication(cnf_simplify(n.target), n.argument)
    return n


if __name__ == "__main__":
    from .frontend_core import expr
    x = expr.parse("((a < 1) --> ((b < 3) && (! ((c > 3) || (d > 3 ) ) )))")
    y = cnf_simplify(x)
    print(y)
