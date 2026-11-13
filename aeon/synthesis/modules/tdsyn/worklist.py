"""Partial programs, typed holes, and path-based (zipper) substitution.

Hole locations are tracked as paths from the root so a single expansion rebuilds
only the spine to that hole (O(depth)), and multi-hole SMT solutions fill every
literal in one tree walk.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field, replace
from enum import Enum, auto

from aeon.core.liquid import LiquidApp, LiquidTerm, LiquidVar
from aeon.core.terms import (
    Abstraction,
    Annotation,
    Application,
    Hole,
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
from aeon.core.types import Type
from aeon.synthesis.grammar.nonterminals import ExpressionDomain, Nonterminal
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name, fresh_counter


class Child(Enum):
    """One step from a term to a direct subterm (zipper context frame)."""

    FUN = auto()
    ARG = auto()
    BODY = auto()
    COND = auto()
    THEN = auto()
    OTHERWISE = auto()
    EXPR = auto()
    VALUE = auto()
    REFINEMENT = auto()


Path = tuple[Child, ...]


@dataclass
class TypedHole:
    """A hole carrying its expected type and the typing context at its position."""

    name: Name
    expected_type: Type
    context: TypingContext
    constraints: list[LiquidTerm] = field(default_factory=list)
    path: Path = ()
    bindings: dict[Name, Type] = field(default_factory=dict)
    domain: ExpressionDomain = ExpressionDomain.TERM
    guards: tuple[LiquidTerm, ...] = ()

    @property
    def nonterminal(self) -> Nonterminal:
        return Nonterminal(self.domain, self.expected_type)


@dataclass
class PartialAST:
    """A partial term with its unfilled holes and current depth."""

    term: Term
    holes: list[TypedHole]
    depth: int
    constraints: list[LiquidTerm] = field(default_factory=list)
    # Keep the original signature: peeled lambdas carry their QTT obligations
    # here, rather than in the value-only typing contexts of individual holes.
    expected_type: Type | None = None
    context: TypingContext | None = None
    check_sketch: Callable[[Term], bool] | None = None

    def qtt_feasible(self) -> bool:
        from aeon.typechecking.linearity import check_linearity

        if self.check_sketch is not None and not self.check_sketch(self.term):
            return False
        if self.expected_type is None:
            return True
        return not check_linearity(Annotation(self.term, self.expected_type), self.context)

    def is_complete(self) -> bool:
        return len(self.holes) == 0


def fresh_hole(
    expected_type: Type,
    context: TypingContext,
    constraints: list[LiquidTerm] | None = None,
    path: Path = (),
    *,
    domain: ExpressionDomain = ExpressionDomain.TERM,
) -> tuple[Hole, TypedHole]:
    """Create a fresh hole with a unique name."""
    name = Name("tdsyn_hole", fresh_counter.fresh())
    loc = SynthesizedLocation("tdsyn")
    hole_term = Hole(name, loc)
    typed_hole = TypedHole(name, expected_type, context, constraints or [], path, domain=domain)
    return hole_term, typed_hole


def locate_holes(term: Term, prefix: Path = ()) -> dict[Name, Path]:
    """Map each synthesis ``Hole`` name under ``term`` to its path from ``prefix``."""
    match term:
        case Hole(name, _):
            return {name: prefix}
        case Application(fun, arg, _):
            return locate_holes(fun, prefix + (Child.FUN,)) | locate_holes(arg, prefix + (Child.ARG,))
        case Abstraction(_, body, _):
            return locate_holes(body, prefix + (Child.BODY,))
        case If(cond, then, otherwise, _):
            return (
                locate_holes(cond, prefix + (Child.COND,))
                | locate_holes(then, prefix + (Child.THEN,))
                | locate_holes(otherwise, prefix + (Child.OTHERWISE,))
            )
        case Annotation(expr, _, _):
            return locate_holes(expr, prefix + (Child.EXPR,))
        case Let(_, var_value, body, _):
            return locate_holes(var_value, prefix + (Child.VALUE,)) | locate_holes(body, prefix + (Child.BODY,))
        case Rec() as rec:
            return locate_holes(rec.var_value, prefix + (Child.VALUE,)) | locate_holes(rec.body, prefix + (Child.BODY,))
        case TypeApplication(body, _, _):
            return locate_holes(body, prefix + (Child.BODY,))
        case TypeAbstraction(_, _, body, _):
            return locate_holes(body, prefix + (Child.BODY,))
        case RefinementApplication(body, refinement, _):
            return locate_holes(body, prefix + (Child.BODY,)) | locate_holes(refinement, prefix + (Child.REFINEMENT,))
        case RefinementAbstraction(_, _, body, _):
            return locate_holes(body, prefix + (Child.BODY,))
        case Literal(_, _, _) | Var(_, _):
            return {}
        case _:
            return {}


def term_at(term: Term, path: Path) -> Term:
    """Read the subtree at a hole's zipper path."""
    attributes = {
        Child.FUN: "fun",
        Child.ARG: "arg",
        Child.BODY: "body",
        Child.COND: "cond",
        Child.THEN: "then",
        Child.OTHERWISE: "otherwise",
        Child.EXPR: "expr",
        Child.VALUE: "var_value",
        Child.REFINEMENT: "refinement",
    }
    for step in path:
        term = getattr(term, attributes[step])
    return term


def substitute_at(term: Term, path: Path, replacement: Term) -> Term:
    """Replace the subterm at ``path``; rebuild only the spine along the path."""
    if not path:
        return replacement
    step, *rest = path
    rest_path = tuple(rest)
    match (term, step):
        case (Application(fun, arg, loc), Child.FUN):
            return Application(substitute_at(fun, rest_path, replacement), arg, loc)
        case (Application(fun, arg, loc), Child.ARG):
            return Application(fun, substitute_at(arg, rest_path, replacement), loc)
        case (Abstraction(var_name, body, loc), Child.BODY):
            return Abstraction(var_name, substitute_at(body, rest_path, replacement), loc)
        case (If(cond, then, otherwise, loc), Child.COND):
            return If(substitute_at(cond, rest_path, replacement), then, otherwise, loc)
        case (If(cond, then, otherwise, loc), Child.THEN):
            return If(cond, substitute_at(then, rest_path, replacement), otherwise, loc)
        case (If(cond, then, otherwise, loc), Child.OTHERWISE):
            return If(cond, then, substitute_at(otherwise, rest_path, replacement), loc)
        case (Annotation(expr, ty, loc), Child.EXPR):
            return Annotation(substitute_at(expr, rest_path, replacement), ty, loc)
        case (Let() as let, Child.VALUE):
            return replace(let, var_value=substitute_at(let.var_value, rest_path, replacement))
        case (Let() as let, Child.BODY):
            return replace(let, body=substitute_at(let.body, rest_path, replacement))
        case (Rec() as rec, Child.VALUE):
            return replace(rec, var_value=substitute_at(rec.var_value, rest_path, replacement))
        case (Rec() as rec, Child.BODY):
            return replace(rec, body=substitute_at(rec.body, rest_path, replacement))
        case (TypeApplication(body, ty, loc), Child.BODY):
            return TypeApplication(substitute_at(body, rest_path, replacement), ty, loc)
        case (TypeAbstraction(name, kind, body, loc), Child.BODY):
            return TypeAbstraction(name, kind, substitute_at(body, rest_path, replacement), loc)
        case (RefinementApplication(body, refinement, loc), Child.BODY):
            return RefinementApplication(substitute_at(body, rest_path, replacement), refinement, loc)
        case (RefinementApplication(body, refinement, loc), Child.REFINEMENT):
            return RefinementApplication(body, substitute_at(refinement, rest_path, replacement), loc)
        case (RefinementAbstraction(name, sort, body, loc), Child.BODY):
            return RefinementAbstraction(name, sort, substitute_at(body, rest_path, replacement), loc)
        case _:
            # Path does not match term shape — search by the hole that should sit here.
            raise ValueError(f"zipper path {path!r} does not match term {term!r}")


def substitute_holes_map(term: Term, mapping: dict[Name, Term]) -> Term:
    """Replace every ``Hole`` whose name appears in ``mapping`` in one walk."""
    if not mapping:
        return term
    match term:
        case Hole(name, _) if name in mapping:
            return mapping[name]
        case Hole(_, _):
            return term
        case Application(fun, arg, loc):
            return Application(substitute_holes_map(fun, mapping), substitute_holes_map(arg, mapping), loc)
        case Abstraction(var_name, body, loc):
            return Abstraction(var_name, substitute_holes_map(body, mapping), loc)
        case If(cond, then, otherwise, loc):
            return If(
                substitute_holes_map(cond, mapping),
                substitute_holes_map(then, mapping),
                substitute_holes_map(otherwise, mapping),
                loc,
            )
        case Annotation(expr, ty, loc):
            return Annotation(substitute_holes_map(expr, mapping), ty, loc)
        case Let() as binding:
            return replace(
                binding,
                var_value=substitute_holes_map(binding.var_value, mapping),
                body=substitute_holes_map(binding.body, mapping),
            )
        case Rec() as rec:
            return replace(
                rec,
                var_value=substitute_holes_map(rec.var_value, mapping),
                body=substitute_holes_map(rec.body, mapping),
            )
        case TypeApplication(body, ty, loc):
            return TypeApplication(substitute_holes_map(body, mapping), ty, loc)
        case TypeAbstraction(name, kind, body, loc):
            return TypeAbstraction(name, kind, substitute_holes_map(body, mapping), loc)
        case RefinementApplication(body, refinement, loc):
            return RefinementApplication(
                substitute_holes_map(body, mapping),
                substitute_holes_map(refinement, mapping),
                loc,
            )
        case RefinementAbstraction(name, sort, body, loc):
            return RefinementAbstraction(name, sort, substitute_holes_map(body, mapping), loc)
        case Literal(_, _, _) | Var(_, _):
            return term
        case _:
            return term


def substitute_hole(term: Term, hole_name: Name, replacement: Term) -> Term:
    """Replace a single hole by name (one-walk map; prefer :func:`substitute_at` when a path is known)."""
    return substitute_holes_map(term, {hole_name: replacement})


def scoped_children(hole: TypedHole, replacement: Term, children: list[TypedHole]) -> list[TypedHole]:
    """Carry the conditions under which each child is actually evaluated."""
    from aeon.synthesis.modules.tdsyn.constraints import symbolic_term

    paths = locate_holes(replacement)
    result = []
    for child in children:
        guards = list(hole.guards)
        term = replacement
        for step in paths.get(child.name, ()):
            if isinstance(term, If) and step in (Child.THEN, Child.OTHERWISE):
                condition = symbolic_term(term.cond, children)
                if condition is None:
                    # Keep unsupported conditions symbolic. The full solver
                    # will defer them instead of asserting both arms at once.
                    condition = LiquidVar(Name("tdsyn_guard", fresh_counter.fresh()))
                if step is Child.OTHERWISE:
                    condition = LiquidApp(Name("!", 0), [condition])
                guards.append(condition)
            term = term_at(term, (step,))
        result.append(replace(child, guards=tuple(guards)))
    return result


def expand_at_hole(
    partial: PartialAST,
    hole: TypedHole,
    replacement: Term,
    new_holes: list[TypedHole],
    depth: int,
) -> PartialAST:
    """Install ``replacement`` at ``hole.path`` and retarget paths of nested holes."""
    new_term = substitute_at(partial.term, hole.path, replacement)
    relative = locate_holes(replacement)
    placed: list[TypedHole] = []
    for h in scoped_children(hole, replacement, new_holes):
        rel = relative.get(h.name, ())
        placed.append(replace(h, path=hole.path + rel))
    from aeon.synthesis.modules.tdsyn.constraints import obligations

    bindings, predicates = obligations(hole, replacement, new_holes)
    remaining = [h for h in partial.holes if h.name != hole.name]
    # Choices made for one argument constrain its siblings too. Copy the state
    # so exploring another candidate cannot mutate this branch's obligations.
    updated = [
        replace(
            h,
            bindings={**h.bindings, **bindings},
            constraints=list(dict.fromkeys([*h.constraints, *predicates])),
        )
        for h in remaining + placed
    ]
    return replace(partial, term=new_term, holes=updated, depth=depth, constraints=list(partial.constraints))
