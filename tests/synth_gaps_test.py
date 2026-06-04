"""Regression tests for synth-mode gaps in aeon.typechecking.typeinfer.

Covers:
- #258 — `synth(If)` (path-sensitive refinement join).
- #259 — `synth(RefinementAbstraction)` (Λρ introduction in synth mode).
"""

from __future__ import annotations

from aeon.core.terms import (
    If,
    Literal,
    RefinementAbstraction,
    Var,
)
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    t_bool,
    t_int,
)
from aeon.sugar.parser import parse_type
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import synth
from aeon.utils.name import Name
from aeon.verification.smt import smt_valid
from tests.driver import check_compile_expr


# ---------------------------------------------------------------------------
# #258 — synth(If)
# ---------------------------------------------------------------------------


def test_synth_if_in_application_arg_typechecks():
    """An if-expression used as an Application argument is ANF-lifted onto a let-RHS,
    which forces synth-mode on the If."""
    source = r"""let f : (x:Int) -> Int = \x -> x in f (if 0 < 1 then 1 else 2)"""
    assert check_compile_expr(source, parse_type("Int"))


def test_synth_if_directly_returns_joined_refinement():
    """`synth` on `if true then 1 else 10` returns an Int refined by the path-sensitive join."""
    ctx = TypingContext()
    term = If(
        Literal(True, t_bool),
        Literal(1, t_int),
        Literal(10, t_int),
    )
    (constraint, ty) = synth(ctx, term)
    # Base type is preserved.
    assert isinstance(ty, RefinedType)
    assert ty.type == t_int
    # The generated VC must be valid (the join is consistent).
    assert smt_valid(constraint)


def test_synth_if_preserves_branch_information_in_join():
    """After synth(If), the result type must imply the disjunction of branch values."""
    # `let r = if (0 < 1) then 1 else 2 in r` should check against `{v:Int | (v == 1) || (v == 2)}`.
    source = r"""let r = (if 0 < 1 then 1 else 2) in r"""
    assert check_compile_expr(source, parse_type("{v:Int | (v == 1) || (v == 2)}"))


def test_synth_if_rejects_unrelated_postcondition():
    """The join doesn't manufacture facts: `{v:Int | v > 100}` is not derivable from
    branches that return 1 or 2."""
    source = r"""let r = (if 0 < 1 then 1 else 2) in r"""
    assert not check_compile_expr(source, parse_type("{v:Int | v > 100}"))


# ---------------------------------------------------------------------------
# #259 — synth(RefinementAbstraction)
# ---------------------------------------------------------------------------


def test_synth_refinement_abstraction_wraps_with_polymorphism():
    """`synth(Λρ:S. e)` returns `forall <ρ:S->Bool>, synth(e)`. We use a literal body so
    we don't depend on the still-open `synth(Abstraction)` gap (#207)."""
    ctx = TypingContext()
    p = Name("p")
    # The sort is the full predicate type (Int -> Bool).
    pred_sort = AbstractionType(Name("_"), t_int, t_bool)
    term = RefinementAbstraction(p, pred_sort, Literal(0, t_int))
    (_, ty) = synth(ctx, term)
    assert isinstance(ty, RefinementPolymorphism)
    assert ty.name == p
    assert ty.sort == pred_sort
    assert isinstance(ty.body, RefinedType)
    assert ty.body.type == t_int


def test_synth_refinement_abstraction_introduces_fresh_uf_in_context():
    """The bound predicate name becomes an uninterpreted function (sort → Bool) inside
    the body. Synth-ing a body that references `p` must succeed."""
    ctx = TypingContext()
    p = Name("p")
    # Λρ:(Int -> Bool). p   — the sort is the full predicate type; Var(p) reads the UF symbol.
    pred_sort = AbstractionType(Name("_"), t_int, t_bool)
    body = Var(p)
    term = RefinementAbstraction(p, pred_sort, body)
    (constraint, ty) = synth(ctx, term)
    assert isinstance(ty, RefinementPolymorphism)
    # Body type is the UF type `(_:Int) -> Bool`, lifted through Var-selfification.
    body_ty = ty.body
    # Var-synth wraps with selfification if the type is base/refined; here it's
    # AbstractionType, which is returned as-is.
    assert isinstance(body_ty, AbstractionType)
    assert body_ty.var_type == t_int
    assert body_ty.type == t_bool


def test_synth_refinement_abstraction_constraint_is_valid():
    """The constraint produced by synth(Λρ) must remain SMT-valid (no spurious obligations
    introduced by the new arm)."""
    ctx = TypingContext()
    p = Name("p")
    # Λρ:(Int -> Bool). 0  — body is a trivially well-typed literal.
    term = RefinementAbstraction(p, AbstractionType(Name("_"), t_int, t_bool), Literal(0, t_int))
    (constraint, _) = synth(ctx, term)
    assert smt_valid(constraint)
