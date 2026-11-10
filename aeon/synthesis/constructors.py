"""Keep deep constructor proofs compact without changing synthesis candidates."""

from dataclasses import replace

from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Literal,
    Rec,
    RefinementAbstraction,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.synthesis.joint import JointCandidate
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter

_loc = SynthesizedLocation("constructor sharing")


def is_constructor_term(term: Term) -> bool:
    """Recognize a registered constructor through applications and instantiation."""
    from aeon.verification.constructor_registry import get_constructor_groups

    while isinstance(term, (Application, TypeApplication, RefinementApplication)):
        term = term.fun if isinstance(term, Application) else term.body
    return isinstance(term, Var) and any(term.name.name in names for names in get_constructor_groups().values())


def bind_constructor_arguments(term: Term) -> Term:
    """Name intermediate data values before checking dependent measure types.

    A nested constructor argument is otherwise substituted into every use of
    its measures, making deep list proofs expand dramatically. Only pure data
    trees are rewritten; calls and control flow keep their evaluation order.
    """

    def spine(value: Term) -> tuple[Term, list[Term]]:
        args = []
        while isinstance(value, Application):
            args.append(value.arg)
            value = value.fun
        return value, list(reversed(args))

    def data_tree(value: Term) -> bool:
        if isinstance(value, (Literal, Var)):
            return True
        return is_constructor_term(value) and all(data_tree(arg) for arg in spine(value)[1])

    if not is_constructor_term(term) or not data_tree(term):
        return term
    bindings: list[tuple[Name, Term]] = []

    def bind(value: Term) -> Var:
        name = Name("_data", fresh_counter.fresh())
        bindings.append((name, value))
        return Var(name, _loc)

    def visit(value: Term) -> Term:
        head, args = spine(value)
        for arg in args:
            if is_constructor_term(arg):
                # Evaluate earlier curried applications before this argument,
                # even if a local function shadows a registered constructor.
                atomic_head = head
                while isinstance(atomic_head, (TypeApplication, RefinementApplication)):
                    atomic_head = atomic_head.body
                if not isinstance(atomic_head, Var):
                    head = bind(head)
                arg = bind(visit(arg))
            head = Application(head, arg, value.loc)
        return head

    result = visit(term)
    if not bindings:
        return term
    for name, value in reversed(bindings):
        result = Let(name, value, result, _loc)
    return result


def prepare_candidate(candidate: Term) -> Term:
    """Share constructor values locally in a validation-only copy.

    Keep bindings inside their original branch or lambda. Runtime evaluation,
    returned candidates, expression-size scores, and resource measurements use
    the original tree. Type/refinement annotations and recursion metadata stay
    intact.
    """
    shared = bind_constructor_arguments(candidate)
    if shared is not candidate:
        return shared

    def updated(**children):
        return (
            replace(candidate, **children)
            if any(value is not getattr(candidate, field) for field, value in children.items())
            else candidate
        )

    match candidate:
        case JointCandidate(terms):
            prepared = tuple(prepare_candidate(term) for term in terms)
            return replace(candidate, terms=prepared) if any(a is not b for a, b in zip(terms, prepared)) else candidate
        case Annotation(expr=expr):
            return updated(expr=prepare_candidate(expr))
        case Application(fun=fun, arg=arg):
            return updated(fun=prepare_candidate(fun), arg=prepare_candidate(arg))
        case Let(var_value=value, body=body) | Rec(var_value=value, body=body):
            return updated(var_value=prepare_candidate(value), body=prepare_candidate(body))
        case If(cond=cond, then=yes, otherwise=no):
            return updated(cond=prepare_candidate(cond), then=prepare_candidate(yes), otherwise=prepare_candidate(no))
        case (
            Abstraction(body=body)
            | TypeAbstraction(body=body)
            | RefinementAbstraction(body=body)
            | TypeApplication(body=body)
            | RefinementApplication(body=body)
        ):
            return updated(body=prepare_candidate(body))
        case _:
            return candidate
