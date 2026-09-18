"""Refinement-aware dead branch elimination (issue #114).

When liquid refinements in scope entail an ``if`` condition (or its negation),
the unreachable branch is removed and a warning may be recorded.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from pathlib import Path

from aeon.core.liquid import LiquidApp, LiquidTerm
from aeon.core.substitutions import liquefy
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
from aeon.core.types import AbstractionType, Type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.utils.location import FileLocation, Location, SynthesizedLocation
from aeon.utils.name import Name
from aeon.verification.vcs import LiquidConstraint


@dataclass(frozen=True)
class DeadBranchWarning:
    """Emitted when a refinement-known-dead ``if`` branch is eliminated."""

    location: Location
    branch: str
    message: str

    def __str__(self) -> str:
        return f"dead {self.branch} branch: {self.message}"


def _negate(liq: LiquidTerm) -> LiquidTerm:
    return LiquidApp(Name("!", 0), [liq])


def _context_entails(ctx: TypingContext, liq: LiquidTerm) -> bool:
    return entailment(ctx, LiquidConstraint(liq))


def _location_in_file(loc: Location, source_path: str | None) -> bool:
    if not isinstance(loc, FileLocation):
        return False
    if source_path is None:
        return True
    if loc.file == source_path:
        return True
    if not loc.file:
        return False
    try:
        return Path(loc.file).resolve() == Path(source_path).resolve()
    except (OSError, ValueError, TypeError):
        return False


def _fold_if(
    ctx: TypingContext,
    cond: Term,
    then: Term,
    otherwise: Term,
    *,
    on_dead_branch: list[DeadBranchWarning] | None,
    source_path: str | None,
) -> Term | None:
    liq_cond = liquefy(cond)
    if liq_cond is None:
        return None
    if _context_entails(ctx, liq_cond):
        if on_dead_branch is not None and _location_in_file(otherwise.loc, source_path):
            on_dead_branch.append(
                DeadBranchWarning(
                    location=otherwise.loc,
                    branch="else",
                    message=(
                        "this branch is unreachable because refinements in scope entail the condition is always true"
                    ),
                )
            )
        return then
    if _context_entails(ctx, _negate(liq_cond)):
        if on_dead_branch is not None and _location_in_file(then.loc, source_path):
            on_dead_branch.append(
                DeadBranchWarning(
                    location=then.loc,
                    branch="then",
                    message=(
                        "this branch is unreachable because refinements in scope entail the condition is always false"
                    ),
                )
            )
        return otherwise
    return None


def _optimize_refinement(
    term: Term,
    ctx: TypingContext,
    *,
    expected_type: Type | None = None,
    on_dead_branch: list[DeadBranchWarning] | None = None,
    source_path: str | None = None,
) -> Term:
    match term:
        case If(cond, then, otherwise):
            folded = _fold_if(
                ctx,
                cond,
                then,
                otherwise,
                on_dead_branch=on_dead_branch,
                source_path=source_path,
            )
            if folded is not None:
                return _optimize_refinement(
                    folded,
                    ctx,
                    expected_type=expected_type,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                )
            return If(
                _optimize_refinement(cond, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
                _optimize_refinement(then, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
                _optimize_refinement(otherwise, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
            )
        case Abstraction(name, body):
            body_ctx = ctx
            if isinstance(expected_type, AbstractionType):
                body_ctx = ctx.with_var(name, expected_type.var_type)
            return Abstraction(
                name,
                _optimize_refinement(
                    body,
                    body_ctx,
                    expected_type=None,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
            )
        case Rec() as rec:
            return _optimize_refinement_bindings(
                rec,
                ctx,
                on_dead_branch=on_dead_branch,
                source_path=source_path,
            )
        case Let() as let:
            return replace(
                let,
                var_value=_optimize_refinement(
                    let.var_value,
                    ctx,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
                body=_optimize_refinement(
                    let.body,
                    ctx,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
            )
        case Application(fun, arg):
            return Application(
                _optimize_refinement(fun, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
                _optimize_refinement(arg, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
            )
        case Annotation(expr, ty):
            return Annotation(
                _optimize_refinement(expr, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
                ty,
            )
        case TypeAbstraction(name, kind, body):
            return TypeAbstraction(
                name,
                kind,
                _optimize_refinement(
                    body, ctx.with_typevar(name, kind), on_dead_branch=on_dead_branch, source_path=source_path
                ),
            )
        case TypeApplication(body, ty):
            return TypeApplication(
                _optimize_refinement(body, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
                ty,
            )
        case RefinementAbstraction(name, sort, body):
            return RefinementAbstraction(
                name,
                sort,
                _optimize_refinement(body, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
            )
        case RefinementApplication(body, refinement):
            return RefinementApplication(
                _optimize_refinement(body, ctx, on_dead_branch=on_dead_branch, source_path=source_path),
                refinement,
            )
        case Literal() | Var() | Hole():
            return term
        case _:
            return term


def _optimize_refinement_bindings(
    core: Term,
    ctx: TypingContext,
    *,
    on_dead_branch: list[DeadBranchWarning] | None = None,
    source_path: str | None = None,
) -> Term:
    match core:
        case Rec() as rec:
            return replace(
                rec,
                var_value=_optimize_refinement(
                    rec.var_value,
                    ctx,
                    expected_type=rec.var_type,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
                body=_optimize_refinement_bindings(
                    rec.body,
                    ctx.with_var(rec.var_name, rec.var_type),
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
            )
        case Let() as let:
            return replace(
                let,
                var_value=_optimize_refinement(
                    let.var_value,
                    ctx,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
                body=_optimize_refinement_bindings(
                    let.body,
                    ctx,
                    on_dead_branch=on_dead_branch,
                    source_path=source_path,
                ),
            )
        case _:
            return _optimize_refinement(
                core,
                ctx,
                on_dead_branch=on_dead_branch,
                source_path=source_path,
            )


def optimize_refinement_bindings(core: Term, ctx: TypingContext) -> Term:
    """Remove ``if`` branches that refinements prove unreachable."""
    return _optimize_refinement_bindings(core, ctx)


def collect_dead_branch_warnings(
    core: Term,
    ctx: TypingContext,
    *,
    source_path: str | None = None,
) -> list[DeadBranchWarning]:
    """Return warnings for every dead branch that refinement optimization would remove."""
    warnings: list[DeadBranchWarning] = []
    _optimize_refinement_bindings(core, ctx, on_dead_branch=warnings, source_path=source_path)
    seen: set[tuple[object, object, str]] = set()
    result: list[DeadBranchWarning] = []
    for warning in warnings:
        loc = warning.location
        key = (loc.get_start(), loc.get_end(), warning.branch)
        if key in seen:
            continue
        seen.add(key)
        result.append(warning)
    return result


def format_location(loc: Location) -> str:
    if isinstance(loc, FileLocation):
        line, col = loc.start
        prefix = f"{loc.file}:" if loc.file else ""
        return f"{prefix}{line}:{col}"
    if isinstance(loc, SynthesizedLocation):
        return str(loc)
    return str(loc)
