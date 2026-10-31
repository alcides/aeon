"""Alpha-stable candidate keys and executable AST cost including helper bodies."""

from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    If,
    Let,
    Literal,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.synthesis.api import InvalidIndividualException


PRIMITIVES = frozenset({"+", "-", "*", "/", "%", "==", "!=", "<", "<=", ">", ">=", "&&", "||", "!", "-->"})


def identity(term: Term, bound=()):
    if isinstance(term, Var):
        return ("bound", bound.index(term.name)) if term.name in bound else ("free", term.name.name, term.name.id)
    if isinstance(term, Literal):
        return ("literal", type(term.value).__name__, repr(term.value), repr(term.type))
    if isinstance(term, (Annotation, TypeApplication)):
        child = term.expr if isinstance(term, Annotation) else term.body
        return (type(term).__name__, repr(term.type), identity(child, bound))
    if isinstance(term, RefinementApplication):
        return ("refinement", identity(term.body, bound), identity(term.refinement, bound))
    if isinstance(term, TypeAbstraction):
        return ("type_lambda", str(term.kind), identity(term.body, bound))
    if isinstance(term, Abstraction):
        return ("lambda", identity(term.body, (term.var_name, *bound)))
    if isinstance(term, Application):
        return ("apply", identity(term.fun, bound), identity(term.arg, bound))
    if isinstance(term, If):
        return ("if", identity(term.cond, bound), identity(term.then, bound), identity(term.otherwise, bound))
    if isinstance(term, Let):
        return (
            "let",
            str(term.multiplicity),
            identity(term.var_value, bound),
            identity(term.body, (term.var_name, *bound)),
        )
    raise InvalidIndividualException("Noisy candidates require complete, nonrecursive executable terms")


def complexity(term: Term, inputs, definitions, bound=frozenset(), expanding=frozenset(), _work=None, _depth=0) -> int:
    if _work is None:
        _work = [10_000]
    _work[0] -= 1
    if _work[0] < 0 or _depth > 200:
        raise InvalidIndividualException("Expanded executable complexity exceeds its work/depth limit")

    def cost(child, local=bound):
        return complexity(child, inputs, definitions, local, expanding, _work, _depth + 1)

    if isinstance(term, Literal):
        return 1
    if isinstance(term, Var):
        if term.name in bound:
            return 1
        if term.name in definitions:
            if term.name in expanding:
                raise InvalidIndividualException("Recursive helper complexity is unsupported")
            return 1 + complexity(
                definitions[term.name], inputs, definitions, frozenset(), expanding | {term.name}, _work, _depth + 1
            )
        if term.name in inputs or (term.name.id == 0 and term.name.name in PRIMITIVES):
            return 1
        raise InvalidIndividualException(f"No executable body available to charge helper {term.name}")
    if isinstance(term, (Annotation, TypeApplication, RefinementApplication)):
        return cost(term.expr if isinstance(term, Annotation) else term.body)
    if isinstance(term, TypeAbstraction):
        return cost(term.body)
    if isinstance(term, Abstraction):
        return 1 + cost(term.body, bound | {term.var_name})
    if isinstance(term, Application):
        return 1 + cost(term.fun) + cost(term.arg)
    if isinstance(term, If):
        return 1 + cost(term.cond) + cost(term.then) + cost(term.otherwise)
    if isinstance(term, Let):
        return 1 + cost(term.var_value) + cost(term.body, bound | {term.var_name})
    raise InvalidIndividualException("Noisy candidates require complete, nonrecursive executable terms")
