"""Cheap necessary conditions for partial programs, without invoking SMT."""

from collections.abc import Iterable

from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidTerm
from aeon.utils.name import Name


def conflicting_integer_equalities(predicates: Iterable[LiquidTerm]) -> bool:
    """Recognize inconsistent conjunctions of exact integer equalities.

    Treat symbolic terms as opaque nodes and union equal nodes. For example,
    size(result)=50, size(result)=size(child), size(child)=0 is impossible.
    Other connectives, inequalities and arithmetic are deliberately left to
    the full solver. In particular, a disjunction must not be flattened.
    """
    parent: dict[LiquidTerm, LiquidTerm] = {}
    values: dict[LiquidTerm, int] = {}

    def root(term: LiquidTerm) -> LiquidTerm:
        if term not in parent:
            parent[term] = term
            if isinstance(term, LiquidLiteralInt):
                values[term] = term.value
        result = term
        while parent[result] != result:
            result = parent[result]
        while parent[term] != term:
            previous = parent[term]
            parent[term] = result
            term = previous
        return result

    pending = list(predicates)
    while pending:
        predicate = pending.pop()
        if not isinstance(predicate, LiquidApp):
            continue
        if predicate.fun == Name("&&", 0) and len(predicate.args) == 2:
            pending.extend(predicate.args)
        elif predicate.fun == Name("==", 0) and len(predicate.args) == 2:
            left, right = map(root, predicate.args)
            if left == right:
                continue
            lv, rv = values.get(left), values.get(right)
            if lv is not None and rv is not None and lv != rv:
                return True
            parent[right] = left
            if lv is None and rv is not None:
                values[left] = rv
    return False
