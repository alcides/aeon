from aeon.core.substitutions import substitute_vartype_in_term, substitution
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import t_bool, t_int


def normal_form(t: Term) -> Term:
    nf = normal_form
    match t:

        case Application(Abstraction(var_name, body), arg):
            return nf(substitution(body, arg, var_name))

        case TypeApplication(TypeAbstraction(vty, kind, body), ty):
            return substitute_vartype_in_term(body, ty, vty)

        case If(Literal(True, _), then, _):
            return then

        case If(Literal(False, _), _, otherwise):
            return otherwise

        # Basic opts

        case Application(Application(Var("&&"), Literal(True, tb)), e):
            return e
        case Application(Application(Var("&&"), Literal(False, tb)), e):
            return Literal(False, tb)
        case Application(Application(Var("&&"), e), Literal(True, tb)):
            return e
        case Application(Application(Var("&&"), e), Literal(False, tb)):
            return Literal(False, tb)

        case Application(Application(Var("||"), Literal(True, tb)), e):
            return Literal(True, tb)
        case Application(Application(Var("||"), Literal(False, tb)), e):
            return e
        case Application(Application(Var("||"), e), Literal(True, tb)):
            return Literal(True, tb)
        case Application(Application(Var("||"), e), Literal(False, tb)):
            return e

        case Application(Application(Var("+"), Literal(0, ti)), e):
            return e
        case Application(Application(Var("+"), e), Literal(0, ti)):
            return e
        case Application(Application(Var("+"), Literal(a, ti)), Literal(b, tb)):
            return Literal(a + b, ti)  # type: ignore

        case Application(Application(Var("-"), e), Literal(0, ti)):
            return e
        case Application(Application(Var("-"), Literal(a, ti)), Literal(b, tb)):
            return Literal(a - b, ti)  # type: ignore
        case Application(Application(Var("-"), x1), x2):
            if x1 == x2:
                return Literal(0, t_int)
            else:
                return t

        case Application(Application(Var("*"), Literal(0, ti)), e):
            return Literal(0, ti)
        case Application(Application(Var("*"), e), Literal(0, ti)):
            return Literal(0, ti)
        case Application(Application(Var("*"), Literal(1, ti)), e):
            return e
        case Application(Application(Var("*"), e), Literal(1, ti)):
            return e
        case Application(Application(Var("*"), Literal(a, ti)), Literal(b, tb)):
            return Literal(a * b, ti)  # type: ignore

        case Application(Application(Var("/"), Literal(0, ti)), e):
            return Literal(0, ti)

        case Application(Application(Var("/"), x1), x2):
            if x1 == x2:
                return Literal(1, t_int)
            else:
                return t

        case Application(Application(Var("%"), Literal(0, ti)), _):
            return Literal(0, t_int)

        case Application(Application(Var("%"), x1), x2):
            if x1 == x2:
                return Literal(0, t_int)
            else:
                return t

        case Application(Application(Var("=="), Literal(a, ti)), Literal(b, tb)):
            return Literal(a == b, t_bool)

        case Application(Application(Var("!="), Literal(a, ti)), Literal(b, tb)):
            return Literal(a != b, t_bool)

        case Application(Application(Var(">"), Literal(a, ti)), Literal(b, tb)):
            return Literal(a > b, t_bool)  # type: ignore

        case Application(Application(Var(">="), Literal(a, ti)), Literal(b, tb)):
            return Literal(a >= b, t_bool)  # type: ignore

        case Application(Application(Var("<"), Literal(a, ti)), Literal(b, tb)):
            return Literal(a < b, t_bool)  # type: ignore

        case Application(Application(Var("<="), Literal(a, ti)), Literal(b, tb)):
            return Literal(a <= b, t_bool)  # type: ignore

        case Literal(_, _):
            return t
        case Var(_):
            return t
        case Annotation(_, _):
            return t
        case Hole(_):
            return t

        case Abstraction(var_name, body):
            return Abstraction(var_name, nf(body))
        case Application(fun, arg):
            return Application(nf(fun), nf(arg))
        case Let(var_name, var_value, body):
            return substitution(body, nf(var_value), var_name)
        case Rec(var_name, var_type, var_value, body):
            return Rec(var_name, var_type, nf(var_value), nf(body))

        case If(cond, then, otherwise):
            return If(nf(cond), nf(then), nf(otherwise))

        case TypeAbstraction(ty, kind, body):
            return TypeAbstraction(ty, kind, nf(body))
        case TypeApplication(body, ty):
            return TypeApplication(nf(body), ty)
    print()
    print("no case for", t, type(t))
    assert False


def optimize(t: Term) -> Term:
    while True:
        nt = normal_form(t)
        if t == nt:
            return nt
        t = nt
