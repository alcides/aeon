from aeon.core.substitutions import substitution
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
)


def strip_type_wrappers(t: Term) -> Term:
    """Peel type-level wrappers, exposing the operational head of a term."""
    while True:
        match t:
            case Annotation(expr, _):
                t = expr
            case TypeApplication(body, _):
                t = body
            case RefinementApplication(body, _):
                t = body
            case TypeAbstraction(_, _, body):
                t = body
            case RefinementAbstraction(_, _, body):
                t = body
            case _:
                return t


def whnf(t: Term) -> Term:
    """Reduce ``t`` to weak-head normal form.

    Strips the administrative wrappers elaboration leaves around values
    (annotations, type/refinement abstractions and applications) and
    beta-reduces any redex sitting at the head. Reduction stops as soon as
    the head is a value (an ``Abstraction``, ``Literal``, ...) or a stuck
    application — it never descends into a lambda body.
    """
    while True:
        match t:
            case Annotation(expr, _):
                t = expr
            case TypeAbstraction(_, _, body):
                t = body
            case RefinementAbstraction(_, _, body):
                t = body
            case TypeApplication(body, _):
                t = body
            case RefinementApplication(body, _):
                t = body
            case Application(fun, arg):
                f = whnf(fun)
                if isinstance(f, Abstraction):
                    t = substitution(f.body, arg, f.var_name)
                else:
                    return Application(f, arg, t.loc)
            case _:
                return t
