"""Static fitness for the expressions inserted at a definition's hole sites."""

from collections.abc import Callable, Iterator
from dataclasses import fields, is_dataclass

from aeon.core.terms import Hole, Let, Rec, Term
from aeon.synthesis.api import InvalidIndividualException
from aeon.utils.name import Name


def _children(term: Term) -> Iterator[tuple[str, Term]]:
    # Only expression children: types, source locations, termination metrics
    # and mutual-companion metadata are not part of the expression tree.
    assert is_dataclass(term)
    for field in fields(term):
        value = getattr(term, field.name)
        if isinstance(value, Term):
            yield field.name, value


def expression_size(term: Term) -> int:
    """Count core expression nodes, including annotations and type wrappers.

    Each literal, variable, application, lambda, conditional or binding counts
    once. Type/refinement expression wrappers also count once; types themselves
    do not. Shared subtrees count once per occurrence, as in the printed program.
    """
    size = 0
    pending = [term]
    while pending:
        current = pending.pop()
        if isinstance(current, Hole):
            raise InvalidIndividualException("cannot measure an unresolved hole")
        size += 1
        pending.extend(child for _, child in _children(current))
    return size


def _definition_value(program: Term, function: Name) -> Term:
    while isinstance(program, (Let, Rec)):
        if program.var_name == function:
            return program.var_value
        program = program.body
    raise InvalidIndividualException(f"size objective cannot find definition {function}")


def make_size_evaluator(program: Term, function: Name) -> Callable[[Term], list[float]]:
    """Record original hole paths, then count only their replacements.

    Substitution preserves the surrounding tree. Paths distinguish fixed syntax
    from synthesized syntax even for nested holes, function-valued holes and
    joint candidates. A definition with several holes contributes their sum;
    holes in other definitions never contribute to its objective.
    """
    paths: list[tuple[str, ...]] = []
    pending: list[tuple[Term, tuple[str, ...]]] = [(_definition_value(program, function), ())]
    while pending:
        term, path = pending.pop()
        if isinstance(term, Hole):
            paths.append(path)
        else:
            pending.extend((child, (*path, name)) for name, child in _children(term))

    def fitness(completed: Term) -> list[float]:
        value = _definition_value(completed, function)
        total = 0
        for path in paths:
            replacement = value
            for name in path:
                replacement = getattr(replacement, name)
            total += expression_size(replacement)
        return [float(total)]

    return fitness
