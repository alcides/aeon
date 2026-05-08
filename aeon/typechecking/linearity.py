"""Linearity (Quantitative Type Theory) check — Phase 2a, syntactic.

Phase 1 (``aeon.core.multiplicity``) gave every binder an optional
multiplicity ``μ ∈ {0, 1, ω}``. This module is the first pass that
*enforces* those annotations.

The check counts the *syntactic* occurrences of a named binder inside its
scope and compares the count against the declared multiplicity:

- ``μ = ω`` (default): no check.
- ``μ = 1`` (linear): the body must reference the name *exactly once*.
- ``μ = 0`` (erased): the body must not reference the name at all.

For ``if`` branches we require the two arms to use a ``1``-bound name
the same number of times — whichever branch is taken at run time must
consume it (or not) consistently. ``Abstraction`` parameters whose
declared multiplicity comes from the surrounding ``AbstractionType``
get the same treatment.

This is the *Linear Haskell* / surface-syntactic flavour of the check.
A more precise QTT version would scale uses through application
parameter multiplicities (so passing a ``1``-bound value into an
``ω``-parameter is rejected); that's Phase 2b.

Pure-``ω`` programs trigger no checks and pay no cost. Existing tests
without any ``0``/``1`` annotation are unaffected.
"""

from __future__ import annotations

from aeon.core.multiplicity import M0, MOmega, Multiplicity
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
from aeon.core.types import AbstractionType, ExistentialType, Type
from aeon.facade.api import (
    ErasedUsedAtRuntimeError,
    LinearBranchMismatchError,
    LinearityError,
    LinearUnusedError,
    LinearUsedTooManyTimesError,
)
from aeon.utils.name import Name


class _BranchMismatch:
    """Sentinel returned by :func:`_count_uses` when an ``if`` uses the
    target name a different number of times in each arm. When this
    sentinel reaches a ``1``-bound binder, we report a
    :class:`LinearBranchMismatchError` with the per-branch counts so
    the user sees the precise diagnostic."""

    def __init__(self, then_uses: int, else_uses: int) -> None:
        self.then_uses = then_uses
        self.else_uses = else_uses


_UseCount = int | _BranchMismatch


def _count_uses(term: Term, name: Name) -> _UseCount:
    """Free occurrences of ``name`` in ``term``, treating ``if`` arms
    that disagree as :class:`_BranchMismatch`. Mismatches are *sticky*:
    any propagation through outer combinators preserves the mismatch.
    """

    def _add(a: _UseCount, b: _UseCount) -> _UseCount:
        if isinstance(a, _BranchMismatch):
            return a
        if isinstance(b, _BranchMismatch):
            return b
        return a + b

    match term:
        case Var(n):
            return 1 if n == name else 0
        case Literal() | Hole():
            return 0
        case Application(fun, arg):
            return _add(_count_uses(fun, name), _count_uses(arg, name))
        case Abstraction(n, body):
            if n == name:
                return 0  # shadowed
            return _count_uses(body, name)
        case Let(n, val, body):
            uses = _count_uses(val, name)
            if n != name:
                uses = _add(uses, _count_uses(body, name))
            return uses
        case Rec(n, _, val, body):
            if n == name:
                return 0  # the binder shadows ``name`` in both val and body
            return _add(_count_uses(val, name), _count_uses(body, name))
        case If(cond, then_t, else_t):
            cond_uses = _count_uses(cond, name)
            then_uses = _count_uses(then_t, name)
            else_uses = _count_uses(else_t, name)
            # Inner mismatches dominate; surface them at the binder.
            if isinstance(then_uses, _BranchMismatch):
                return then_uses
            if isinstance(else_uses, _BranchMismatch):
                return else_uses
            if then_uses != else_uses:
                # We're directly inside an `if` whose arms disagree about
                # this variable. Either branch could be taken at run
                # time, so we can't certify a single linear count.
                return _BranchMismatch(then_uses, else_uses)
            return _add(cond_uses, then_uses)
        case Annotation(expr, _):
            return _count_uses(expr, name)
        case TypeApplication(body, _) | RefinementApplication(body, _):
            return _count_uses(body, name)
        case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
            return _count_uses(body, name)
        case _:
            return 0


def _check_binder(
    name: Name,
    multiplicity: Multiplicity,
    body: Term,
    term: Term,
    errors: list[LinearityError],
) -> None:
    """Enforce ``multiplicity`` on ``name`` against its uses in ``body``.

    ``term`` is the enclosing AST node — used only for the error's
    location. Skips the check when ``multiplicity`` is ``MOmega``.
    """
    if multiplicity is MOmega:
        return

    uses = _count_uses(body, name)

    if isinstance(uses, _BranchMismatch):
        # An ``if`` deep in the body uses ``name`` differently in each
        # arm. For ``1``-bound names this is the canonical "leaks
        # only on one path" diagnostic; for ``0``-bound names a
        # mismatch still implies *some* runtime use.
        if multiplicity is M0:
            errors.append(ErasedUsedAtRuntimeError(name=name, term=term))
        else:
            errors.append(
                LinearBranchMismatchError(name=name, then_uses=uses.then_uses, else_uses=uses.else_uses, term=term)
            )
        return

    if multiplicity is M0:
        if uses > 0:
            errors.append(ErasedUsedAtRuntimeError(name=name, term=term))
        return

    # multiplicity is M1
    if uses == 0:
        errors.append(LinearUnusedError(name=name, declared=multiplicity, term=term))
        return
    if uses > 1:
        errors.append(LinearUsedTooManyTimesError(name=name, declared=multiplicity, actual_uses=uses, term=term))
        return


def _abstraction_param_multiplicity(declared_type: Type | None) -> Multiplicity:
    """Pull the parameter's declared multiplicity off an ``AbstractionType``
    if we know it (e.g. from the enclosing ``Rec``'s annotation). Defaults
    to ``MOmega`` when the type is not known or not an abstraction."""
    ty = declared_type
    while isinstance(ty, ExistentialType):
        ty = ty.body
    if isinstance(ty, AbstractionType):
        return ty.multiplicity
    return MOmega


def check_linearity(term: Term) -> list[LinearityError]:
    """Walk ``term`` and return any linearity violations. Empty list ⇔ OK.

    The walk also descends into binders so violations are reported for
    every nested scope. Each violation is reported once per offending
    binder — ``check_type_errors`` will surface them after the constraint
    check completes.
    """
    errors: list[LinearityError] = []

    def visit(node: Term, declared_param_mult: Multiplicity = MOmega) -> None:
        match node:
            case Literal() | Var() | Hole():
                return
            case Annotation(expr, _):
                visit(expr)
            case Application(fun, arg):
                visit(fun)
                visit(arg)
            case Abstraction(name, body):
                # The parameter's multiplicity comes from the enclosing
                # ``AbstractionType``, surfaced via ``declared_param_mult``.
                _check_binder(name, declared_param_mult, body, node, errors)
                visit(body)
            case Let(name, val, body, _, mult):
                _check_binder(name, mult, body, node, errors)
                visit(val)
                visit(body)
            case Rec(name, var_type, val, body, _, _, mult):
                _check_binder(name, mult, body, node, errors)
                # When ``val`` is itself an ``Abstraction``, propagate the
                # function's parameter multiplicity through.
                if isinstance(val, Abstraction):
                    visit(val, _abstraction_param_multiplicity(var_type))
                else:
                    visit(val)
                visit(body)
            case If(cond, then_t, else_t):
                visit(cond)
                visit(then_t)
                visit(else_t)
            case TypeApplication(body, _) | RefinementApplication(body, _):
                visit(body)
            case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
                visit(body)
            case _:
                return

    visit(term)
    return errors
