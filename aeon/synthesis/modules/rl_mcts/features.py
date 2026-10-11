"""Stable bag-of-symbols and length-two term walks (paper section 3.3)."""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from hashlib import blake2b

from aeon.core.liquid import LiquidTerm
from aeon.core.terms import Application, Hole, Term
from aeon.core.types import Type
from aeon.utils.name import Name


@dataclass(frozen=True)
class Syntax:
    label: str
    children: tuple[Syntax, ...] = ()

    def holes(self) -> int:
        return int(self.label.startswith("hole:")) + sum(c.holes() for c in self.children)


def syntax(value: object, names: dict[Name, str] | None = None) -> Syntax:
    """Ignore locations/fresh hole ids; retain operator and variable identity.

    Names are numbered by encounter order within a shared specification/state
    environment, so fresh compiler ids cannot change the model's vocabulary.
    Curried applications are flattened to ordinary operator term walks.
    """
    if names is None:
        names = {}
    if isinstance(value, Hole):
        return Syntax("hole:term")
    if isinstance(value, Name):
        if value not in names:
            names[value] = f"{value.name}:{len(names)}"
        return Syntax(names[value])
    if isinstance(value, Application):
        args: list[Term] = []
        head: Term = value
        while isinstance(head, Application):
            args.append(head.arg)
            head = head.fun
        return Syntax("apply", (syntax(head, names), *(syntax(a, names) for a in reversed(args))))
    if isinstance(value, (Term, Type, LiquidTerm)) and is_dataclass(value):
        children = tuple(
            syntax(getattr(value, f.name), names)
            for f in fields(value)
            if f.name not in {"loc", "multiplicity", "is_recursive"}
        )
        return Syntax(type(value).__name__, children)
    if isinstance(value, (list, tuple)):
        return Syntax("sequence", tuple(syntax(v, names) for v in value))
    return Syntax(f"{type(value).__name__}:{value}")


def term_features(tree: Syntax, bins: int = 4093) -> list[float]:
    if bins < 1:
        raise ValueError("feature hash base must be positive")
    result = [0.0] * bins

    def add(word: str) -> None:
        index = int.from_bytes(blake2b(word.encode(), digest_size=8).digest(), "big") % bins
        result[index] += 1.0

    def walk(node: Syntax) -> None:
        add(f"symbol:{node.label}")
        for child in node.children:
            add(f"walk:{node.label}\0{child.label}")
            walk(child)

    walk(tree)
    return result


def value_features(spec: Syntax, state: Syntax, bins: int = 4093) -> list[float]:
    return term_features(spec, bins) + term_features(state, bins)


def policy_features(spec: Syntax, state: Syntax, child: Syntax, bins: int = 4093) -> list[float]:
    return value_features(spec, state, bins) + term_features(child, bins)
