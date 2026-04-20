from __future__ import annotations

from dataclasses import dataclass, field

from aeon.core.liquid import LiquidTerm
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
    If,
    Let,
    Literal,
    Rec,
    RefinementApplication,
    Term,
    TypeAbstraction,
    TypeApplication,
    Var,
)
from aeon.core.types import Type
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter


@dataclass
class TypedHole:
    """A hole carrying its expected type and the typing context at its position."""

    name: Name
    expected_type: Type
    context: TypingContext
    constraints: list[LiquidTerm] = field(default_factory=list)


@dataclass
class PartialAST:
    """A partial term with its unfilled holes and current depth."""

    term: Term
    holes: list[TypedHole]
    depth: int
    constraints: list[LiquidTerm] = field(default_factory=list)

    def is_complete(self) -> bool:
        return len(self.holes) == 0


def fresh_hole(
    expected_type: Type,
    context: TypingContext,
    constraints: list[LiquidTerm] | None = None,
) -> tuple[Hole, TypedHole]:
    """Create a fresh hole with a unique name."""
    name = Name("tdsyn_hole", fresh_counter.fresh())
    loc = SynthesizedLocation("tdsyn")
    hole_term = Hole(name, loc)
    typed_hole = TypedHole(name, expected_type, context, constraints or [])
    return hole_term, typed_hole


def substitute_hole(term: Term, hole_name: Name, replacement: Term) -> Term:
    """Replace a Hole node with the given name by the replacement term."""
    match term:
        case Hole(name, _) if name == hole_name:
            return replacement
        case Hole(_, _):
            return term
        case Application(fun, arg, loc):
            return Application(
                substitute_hole(fun, hole_name, replacement),
                substitute_hole(arg, hole_name, replacement),
                loc,
            )
        case Abstraction(var_name, body, loc):
            return Abstraction(var_name, substitute_hole(body, hole_name, replacement), loc)
        case If(cond, then, otherwise, loc):
            return If(
                substitute_hole(cond, hole_name, replacement),
                substitute_hole(then, hole_name, replacement),
                substitute_hole(otherwise, hole_name, replacement),
                loc,
            )
        case Annotation(expr, ty, loc):
            return Annotation(substitute_hole(expr, hole_name, replacement), ty, loc)
        case Let(var_name, var_value, body, loc):
            return Let(
                var_name,
                substitute_hole(var_value, hole_name, replacement),
                substitute_hole(body, hole_name, replacement),
                loc,
            )
        case Rec(var_name, var_type, var_value, body, loc):
            return Rec(
                var_name,
                var_type,
                substitute_hole(var_value, hole_name, replacement),
                substitute_hole(body, hole_name, replacement),
                loc,
            )
        case TypeApplication(body, ty, loc):
            return TypeApplication(substitute_hole(body, hole_name, replacement), ty, loc)
        case TypeAbstraction(name, kind, body, loc):
            return TypeAbstraction(name, kind, substitute_hole(body, hole_name, replacement), loc)
        case RefinementApplication(body, refinement, loc):
            return RefinementApplication(
                substitute_hole(body, hole_name, replacement),
                substitute_hole(refinement, hole_name, replacement),
                loc,
            )
        case Literal(_, _, _) | Var(_, _):
            return term
        case _:
            return term
