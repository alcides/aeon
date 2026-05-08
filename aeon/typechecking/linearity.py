"""Linearity (Quantitative Type Theory) check — Phase 2b, scaled tallies.

Phase 1 (``aeon.core.multiplicity``) gave every binder an optional
multiplicity ``μ ∈ {0, 1, ω}``. Phase 2a was the syntactic-occurrence
flavour — *Linear Haskell* style. Phase 2b (this module) tracks per-name
*tallies* drawn from the QTT semiring and **scales** them through
application by the parameter's declared multiplicity:

    tally(f e) = tally(f) ⊕ μ_param ⊗ tally(e)

This catches the canonical QTT discipline error — passing a ``1``-bound
value into an ``ω``-parameter — that the syntactic count silently
admitted.

For each binder ``μ x = e`` we compare ``tally(body)[x]`` against ``μ``:

- ``μ = ω`` (default): no check; the variable can be used freely.
- ``μ = 1``: the body's tally for ``x`` must be exactly ``1``. ``0``
  raises :class:`LinearUnusedError`; ``ω`` raises
  :class:`LinearUsedTooManyTimesError` (the syntactic count is
  preserved alongside the multiplicity for diagnostics).
- ``μ = 0``: the body's tally for ``x`` must be ``0``. Any non-zero use
  raises :class:`ErasedUsedAtRuntimeError`.

For ``if`` arms we require the two branches to agree on every name's
multiplicity — whichever branch is taken at run time must consume the
binders the same way. Disagreements bubble up as :class:`_Mismatch`
sentinels and convert to :class:`LinearBranchMismatchError` at the
binder.

Pure-``ω`` programs trigger no checks and pay no cost. Existing tests
without any ``0``/``1`` annotation are unaffected.
"""

from __future__ import annotations

from dataclasses import dataclass

from aeon.core.multiplicity import M0, M1, MN, MOmega, Multiplicity, add, mul
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
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


@dataclass
class _Mismatch:
    """Sticky sentinel for an ``if`` whose arms disagree about a name's
    multiplicity. Flows up through :func:`_tally_add` / :func:`_tally_scale`
    until a binder check observes it and emits the appropriate diagnostic.

    We keep an integer count per branch (``then_uses``, ``else_uses``) for
    the user-facing error message; the multiplicity-level disagreement
    drives the actual check."""

    then_uses: int
    else_uses: int


class _Bottom:
    """Sticky sentinel produced by *native FFI bodies* (``native "..."`` /
    ``native_import "..."``). The native body opaquely uses every name in
    scope at whatever multiplicity satisfies the surrounding binder — so
    ``_Bottom`` flows like ``false`` does for refinements: it satisfies any
    declared discipline (``M0``, ``M1``, ``MOmega``, ``MN``).

    Sticky in addition and scaling so it survives propagation up through
    intermediate combinators."""

    _instance: _Bottom | None = None

    def __new__(cls) -> _Bottom:
        # Single instance — comparisons use ``is`` throughout the module.
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __repr__(self) -> str:  # pragma: no cover
        return "⊥"


_BOTTOM = _Bottom()


# Per-name usage record. ``count`` is the syntactic occurrence count
# (used for diagnostics); ``mult`` is the QTT multiplicity that drives
# the binder check. ``_Mismatch`` and ``_Bottom`` flow in place of either.
_Usage = Multiplicity | _Mismatch | _Bottom
Tally = dict[Name, _Usage]
_Counts = dict[Name, int]


def _peel_existential(ty: Type | None) -> Type | None:
    """Strip outer ``ExistentialType`` wrappers; binders don't change a
    type's parameter multiplicity."""
    while isinstance(ty, ExistentialType):
        ty = ty.body
    return ty


def _add_usage(a: _Usage, b: _Usage) -> _Usage:
    # ``_Bottom`` and ``_Mismatch`` are sticky and dominate addition.
    if isinstance(a, _Bottom) or isinstance(b, _Bottom):
        return _BOTTOM
    if isinstance(a, _Mismatch):
        return a
    if isinstance(b, _Mismatch):
        return b
    return add(a, b)


def _scale_usage(scale: Multiplicity, b: _Usage) -> _Usage:
    if isinstance(b, _Bottom):
        return _BOTTOM
    if isinstance(b, _Mismatch):
        return b
    return mul(scale, b)


def _tally_add(t1: Tally, t2: Tally) -> Tally:
    out: Tally = dict(t1)
    for n, m in t2.items():
        out[n] = _add_usage(out.get(n, M0), m)
    return out


def _tally_scale(scale: Multiplicity, t: Tally) -> Tally:
    if scale is M1 or scale is MN:
        # ``MN`` is the identity on the caller side: a polymorphic-mult
        # function lets the argument's tally flow through unchanged.
        return dict(t)
    if scale is M0:
        # Erased: every name's contribution is zero (except ``_Bottom``,
        # which stays sticky).
        return {n: (m if isinstance(m, _Bottom) else M0) for n, m in t.items()}
    # ω scaling forces every nonzero usage to ω.
    return {n: _scale_usage(scale, m) for n, m in t.items()}


def _counts_add(c1: _Counts, c2: _Counts) -> _Counts:
    out: _Counts = dict(c1)
    for n, k in c2.items():
        out[n] = out.get(n, 0) + k
    return out


def _counts_scale(scale: Multiplicity, c: _Counts) -> _Counts:
    if scale is M0:
        return {n: 0 for n in c}
    # 1, ω, and n all leave the integer count alone — the multiplicity
    # track captures the QTT-level scaling, the count is purely
    # diagnostic.
    return dict(c)


def _drop(tally: Tally, counts: _Counts, name: Name) -> tuple[Tally, _Counts]:
    nt = {n: m for n, m in tally.items() if n != name}
    nc = {n: k for n, k in counts.items() if n != name}
    return nt, nc


def _alias_project(
    tally: Tally,
    counts: _Counts,
    name: Name,
    val: Term,
) -> tuple[Tally, _Counts]:
    """Phase 3: when a let binds ``name`` to a bare ``Var(x)``, the binder
    is just an alias. Any uses of ``name`` in the body should be folded
    back into ``x`` so the outer scope sees them too — otherwise a linear
    ``x`` aliased through ``let g = x`` and consumed twice via ``g`` would
    slip past the linearity check.

    For non-``Var`` values we simply drop ``name`` (no alias to chase)."""
    if not isinstance(val, Var):
        return _drop(tally, counts, name)
    target = val.name
    if name == target:
        # ``let x = x`` — projecting onto self is a no-op.
        return _drop(tally, counts, name)
    n_use = tally.get(name, M0)
    n_count = counts.get(name, 0)
    nt = {k: v for k, v in tally.items() if k != name}
    nc = {k: v for k, v in counts.items() if k != name}
    if n_use is not M0:
        nt[target] = _add_usage(nt.get(target, M0), n_use)
        nc[target] = nc.get(target, 0) + n_count
    return nt, nc


@dataclass
class _Walker:
    """Walks a core term tracking per-name multiplicities and counts.

    ``var_types`` maps every in-scope *typed* name to its type so
    application can read off the parameter multiplicity for scaling.
    ``in_scope`` is the broader set of names visible at this point,
    including binders whose types we don't track — used by native FFI
    bodies to spread ``_Bottom`` across every name in scope.
    """

    var_types: dict[Name, Type]
    errors: list[LinearityError]
    in_scope: frozenset[Name] = frozenset()

    def with_var(self, name: Name, ty: Type | None) -> _Walker:
        new_types = dict(self.var_types)
        if ty is not None:
            new_types[name] = ty
        elif name in new_types:
            # Shadowed without a known type: drop the outer binding so
            # the inner one isn't accidentally consulted.
            del new_types[name]
        return _Walker(
            var_types=new_types,
            errors=self.errors,
            in_scope=self.in_scope | {name},
        )

    def term_type(self, term: Term) -> Type | None:
        """Best-effort type inference for QTT scaling. ``None`` means the
        type is unknown; callers fall back to the conservative default
        (scaling by ``M1``, i.e. preserving the syntactic count)."""
        match term:
            case Var(n):
                return self.var_types.get(n)
            case Annotation(_, ty):
                return ty
            case Literal(_, ty):
                return ty
            case Application(fun, _):
                ft = _peel_existential(self.term_type(fun))
                if isinstance(ft, AbstractionType):
                    return ft.type
                return None
            case _:
                return None

    def _native_bottom_tally(self) -> tuple[Tally, _Counts]:
        """Tally for a ``native "..."`` / ``native_import "..."`` call:
        every name in scope gets ``_Bottom`` so any surrounding linear
        binder check passes. The native body is opaque to Aeon's
        analysis; the caller-side declaration is what carries the
        discipline."""
        return ({n: _BOTTOM for n in self.in_scope}, {})

    def tally(self, term: Term) -> tuple[Tally, _Counts]:
        if _is_native_ffi_call(term):
            return self._native_bottom_tally()
        match term:
            case Var(n):
                return ({n: M1}, {n: 1})
            case Literal() | Hole():
                return ({}, {})
            case Annotation(expr, _):
                return self.tally(expr)
            case Application(fun, arg):
                ft, fc = self.tally(fun)
                at, ac = self.tally(arg)
                fun_ty = _peel_existential(self.term_type(fun))
                if isinstance(fun_ty, AbstractionType):
                    pmult = fun_ty.multiplicity
                else:
                    # Unknown function type: don't penalise — scale by 1
                    # so the syntactic-count semantics from Phase 2a is
                    # preserved as a floor.
                    pmult = M1
                return (
                    _tally_add(ft, _tally_scale(pmult, at)),
                    _counts_add(fc, _counts_scale(pmult, ac)),
                )
            case Abstraction(n, body):
                inner = self.with_var(n, None)
                bt, bc = inner.tally(body)
                return _drop(bt, bc, n)
            case Let(n, val, body, _, _):
                inner = self.with_var(n, None)
                bt, bc = inner.tally(body)
                if isinstance(val, Var) and val.name != n:
                    # Phase 3 alias projection: ``let n = x`` is pure
                    # renaming. Substitute ``n := x`` in body's tally and
                    # *don't* add a separate ``vt`` contribution — the
                    # bare read of ``x`` in val position is the same use
                    # as the (now-redirected) reads of ``n`` in body.
                    bt, bc = _alias_project(bt, bc, n, val)
                    return (bt, bc)
                # Non-alias val: tally val + body-without-name as usual.
                # We don't scale val by μ here: the tally we return is
                # what the *enclosing* scope sees, and the binder
                # declaration bounds usage of ``n`` *within* body, not
                # the let's dependence on outer free vars.
                vt, vc = self.tally(val)
                bt, bc = _drop(bt, bc, n)
                return (_tally_add(vt, bt), _counts_add(vc, bc))
            case Rec(n, var_type, val, body, _, _, _):
                inner = self.with_var(n, var_type)
                vt, vc = inner.tally(val)
                bt, bc = inner.tally(body)
                vt, vc = _drop(vt, vc, n)
                bt, bc = _drop(bt, bc, n)
                return (_tally_add(vt, bt), _counts_add(vc, bc))
            case If(cond, then_t, else_t):
                ct, cc = self.tally(cond)
                tt, tc = self.tally(then_t)
                et, ec = self.tally(else_t)
                merged_t, merged_c = _branch_merge(tt, tc, et, ec)
                return (_tally_add(ct, merged_t), _counts_add(cc, merged_c))
            case TypeApplication(body, _) | RefinementApplication(body, _):
                return self.tally(body)
            case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
                return self.tally(body)
            case _:
                return ({}, {})


def _branch_merge(
    tt: Tally,
    tc: _Counts,
    et: Tally,
    ec: _Counts,
) -> tuple[Tally, _Counts]:
    """Merge the two arms of an ``if``. Names whose multiplicity disagrees
    between branches become ``_Mismatch`` so the enclosing binder can
    report a precise branch-mismatch error.

    The integer counts use ``max`` of the two arms so the diagnostic
    reflects the worse branch."""
    keys = set(tt) | set(et)
    out_t: Tally = {}
    for k in keys:
        v_then = tt.get(k, M0)
        v_else = et.get(k, M0)
        if isinstance(v_then, _Bottom) or isinstance(v_else, _Bottom):
            # If either arm produces ``_Bottom`` (a native FFI body), the
            # whole branch is satisfied for this name.
            out_t[k] = _BOTTOM
        elif isinstance(v_then, _Mismatch):
            out_t[k] = v_then
        elif isinstance(v_else, _Mismatch):
            out_t[k] = v_else
        elif v_then == v_else:
            out_t[k] = v_then
        else:
            # The arms disagree at the multiplicity level. Convert to a
            # sticky mismatch carrying the *integer* counts so the user
            # sees concrete numbers in the diagnostic.
            out_t[k] = _Mismatch(then_uses=tc.get(k, 0), else_uses=ec.get(k, 0))
    out_c: _Counts = {}
    for k in set(tc) | set(ec):
        out_c[k] = max(tc.get(k, 0), ec.get(k, 0))
    return out_t, out_c


def _check_binder(
    name: Name,
    multiplicity: Multiplicity,
    body_tally: Tally,
    body_counts: _Counts,
    term: Term,
    errors: list[LinearityError],
) -> None:
    """Enforce ``multiplicity`` on ``name`` against the QTT-scaled tally
    for the body. ``term`` is the enclosing AST node — only used for the
    error's location. Skips the check when ``multiplicity`` is ``MOmega``
    or ``MN`` (polymorphic — body discipline is not enforced).
    """
    if multiplicity is MOmega or multiplicity is MN:
        return

    use = body_tally.get(name, M0)
    count = body_counts.get(name, 0)

    # ``_Bottom`` (native FFI body) satisfies any required multiplicity —
    # the body is opaque and the caller-side declaration carries the
    # discipline.
    if isinstance(use, _Bottom):
        return

    if isinstance(use, _Mismatch):
        if multiplicity is M0:
            errors.append(ErasedUsedAtRuntimeError(name=name, term=term))
        else:
            errors.append(
                LinearBranchMismatchError(
                    name=name,
                    then_uses=use.then_uses,
                    else_uses=use.else_uses,
                    term=term,
                )
            )
        return

    if multiplicity is M0:
        if use is not M0:
            errors.append(ErasedUsedAtRuntimeError(name=name, term=term))
        return

    # multiplicity is M1
    if use is M0:
        errors.append(LinearUnusedError(name=name, declared=multiplicity, term=term))
        return
    if use is MOmega:
        # ω can mean either "more than once syntactically" or "passed into
        # an ω-parameter that may consume it any number of times". The
        # integer count tells the user *which*; if we have no count, fall
        # back to 2 to signal "more than 1".
        actual = count if count >= 2 else 2
        errors.append(
            LinearUsedTooManyTimesError(
                name=name,
                declared=multiplicity,
                actual_uses=actual,
                term=term,
            )
        )
        return
    # use is M1 — exactly the linear obligation. OK.


def _abstraction_param_multiplicity(declared_type: Type | None) -> Multiplicity:
    """Pull the parameter's declared multiplicity off an ``AbstractionType``
    if we know it (e.g. from the enclosing ``Rec``'s annotation). Defaults
    to ``MOmega`` when the type is not known or not an abstraction."""
    ty = _peel_existential(declared_type)
    if isinstance(ty, AbstractionType):
        return ty.multiplicity
    return MOmega


def _abstraction_body_type(declared_type: Type | None) -> Type | None:
    ty = _peel_existential(declared_type)
    if isinstance(ty, AbstractionType):
        return ty.type
    return None


def _is_native_ffi_call(t: Term) -> bool:
    """Recognise a single ``native "..."`` / ``native_import "..."`` call
    site. The linearity check can't see through the FFI string, so any
    parameter referenced only inside the native code looks unused — we
    feed back ``_Bottom`` for every name in scope at this point so the
    caller-side declared discipline is the only thing checked."""
    head: Term = t
    while isinstance(head, (Annotation, TypeApplication, RefinementApplication)):
        head = head.expr if isinstance(head, Annotation) else head.body
    if isinstance(head, Var) and head.name.name in {"native", "native_import"}:
        return True
    if isinstance(head, Application):
        cur: Term = head
        while isinstance(cur, Application):
            cur = cur.fun
        while isinstance(cur, (TypeApplication, RefinementApplication)):
            cur = cur.body
        if isinstance(cur, Var) and cur.name.name in {"native", "native_import"}:
            return True
    return False


def check_linearity(term: Term, ctx: TypingContext | None = None) -> list[LinearityError]:
    """Walk ``term`` and return any linearity violations. Empty list ⇔ OK.

    ``ctx`` is the (constraint-checked) typing context — when supplied,
    free-variable types are read from it so application sites scale by
    the *declared* parameter multiplicity. Without a context the walker
    treats every external function as ``M1``-parameterised, which gives
    the syntactic-count semantics from Phase 2a.

    The walk descends into binders so violations are reported for every
    nested scope. Each violation is reported once per offending binder —
    ``check_type_errors`` surfaces them after the constraint check.
    """
    errors: list[LinearityError] = []
    initial_types: dict[Name, Type] = {}
    if ctx is not None:
        for n, t in ctx.vars():
            initial_types[n] = t

    def visit(node: Term, walker: _Walker, declared_param_mult: Multiplicity = MOmega) -> None:
        match node:
            case Literal() | Var() | Hole():
                return
            case Annotation(expr, _):
                visit(expr, walker)
            case Application(fun, arg):
                visit(fun, walker)
                visit(arg, walker)
            case Abstraction(name, body):
                inner = walker.with_var(name, None)
                bt, bc = inner.tally(body)
                _check_binder(name, declared_param_mult, bt, bc, node, errors)
                visit(body, inner)
            case Let(name, val, body, _, mult):
                inner = walker.with_var(name, None)
                bt, bc = inner.tally(body)
                _check_binder(name, mult, bt, bc, node, errors)
                visit(val, walker)
                visit(body, inner)
            case Rec(name, var_type, val, body, _, _, mult):
                inner = walker.with_var(name, var_type)
                bt, bc = inner.tally(body)
                _check_binder(name, mult, bt, bc, node, errors)
                if isinstance(val, Abstraction):
                    # When ``val`` is an ``Abstraction``, propagate the
                    # function's parameter multiplicity through.
                    inner_param_mult = _abstraction_param_multiplicity(var_type)
                    visit(val, inner, inner_param_mult)
                else:
                    visit(val, inner)
                visit(body, inner)
            case If(cond, then_t, else_t):
                visit(cond, walker)
                visit(then_t, walker)
                visit(else_t, walker)
            case TypeApplication(body, _) | RefinementApplication(body, _):
                visit(body, walker)
            case TypeAbstraction(_, _, body) | RefinementAbstraction(_, _, body):
                visit(body, walker)
            case _:
                return

    root = _Walker(
        var_types=initial_types,
        errors=errors,
        in_scope=frozenset(initial_types),
    )
    visit(term, root)
    return errors
