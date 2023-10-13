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
from aeon.typechecking.context import TypingContext


def get_holes(term: Term) -> list[str]:
    """Returns the names of holes in a particular term."""
    match term:
        case Hole(name=name):
            return [name]
        case Hole(name=name):
            return [name]
        case Literal(_):
            return []
        case Var(_):
            return []
        case Annotation(expr=expr, type=_):
            return get_holes(expr)
        case Application(fun=fun, arg=arg):
            return get_holes(fun) + get_holes(arg)
        case If(cond=cond, then=then, otherwise=otherwise):
            return get_holes(cond) + get_holes(then) + get_holes(otherwise)
        case Abstraction(var_name=_, body=body):
            return get_holes(body)
        case Let(var_name=_, var_value=value, body=body):
            return get_holes(value) + get_holes(body)
        case Rec(var_name=_, var_type=_, var_value=value, body=body):
            return get_holes(value) + get_holes(body)
        case TypeApplication(body=body, type=_):
            return get_holes(body)
        case TypeAbstraction(name=_, kind=_, body=body):
            return get_holes(body)
        case _:
            assert False


def incomplete_functions_and_holes(ctx: TypingContext, term: Term) -> list[tuple[str, list[str]]]:
    """Given a typing context and a term, this function identifies which top-level functions have holes, and returns a list of holes in each function."""
    match term:
        case Rec(var_name=name, var_type=_, var_value=value, body=body):
            holes: list[str] = get_holes(value)
            if holes:
                return [(name, holes)] + incomplete_functions_and_holes(ctx, body)
            else:
                return incomplete_functions_and_holes(ctx, body)
        case _:
            print("unknown", term)
            return []
