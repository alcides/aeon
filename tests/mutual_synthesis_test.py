"""Co-synthesis of holes inside a ``mutual`` group (issue #397, MR category).

aeon synthesizes one hole at a time, validating the whole program with the
liquid typechecker. For a ``mutual`` block each member is a top-level binding
(so both become synthesis targets), and the new ``companions`` machinery keeps
the *siblings* in scope while a member's hole is identified and synthesised — the
declared refined type over-approximates each (co-synthesised) callee's
behaviour. These tests pin that plumbing and an end-to-end co-synthesis.
"""

from __future__ import annotations

from aeon.core.types import top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type
from aeon.core.types import Top


def _driver() -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="enumerative",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=10,
        no_main=True,
    )
    return AeonDriver(cfg)


MUTUAL_HOLES = """
mutual
  def f (n: {x:Int | x >= 0}) : {r:Int | r >= 0} decreasing_by [n] := ?hf;
  def g (n: {x:Int | x >= 0}) : {r:Int | r >= 0} decreasing_by [n] := ?hg;
end
"""


def test_both_mutual_members_are_targets():
    d = _driver()
    assert d.parse(aeon_code=MUTUAL_HOLES, filename="<t>") == []
    targets = incomplete_functions_and_holes(d.typing_ctx, d.core)
    names = {fn.name for fn, _ in targets}
    assert names == {"f", "g"}, names
    # Exactly one hole per member.
    assert all(len(holes) == 1 for _, holes in targets)


def test_sibling_in_scope_at_each_hole():
    """The companion (sibling) must be visible in the typing context of each
    member's hole, so a candidate may call it."""
    d = _driver()
    assert d.parse(aeon_code=MUTUAL_HOLES, filename="<t>") == []
    targets = incomplete_functions_and_holes(d.typing_ctx, d.core)
    info = get_holes_info(d.typing_ctx, d.core, top, targets, refined_types=True)
    by_fun = {fn.name: holes[0] for fn, holes in targets}
    # f's hole context knows g, and vice versa.
    _, ctx_f = info[by_fun["f"]]
    _, ctx_g = info[by_fun["g"]]
    ctx_f_names = {n.name for n, _ in ctx_f.vars()}
    ctx_g_names = {n.name for n, _ in ctx_g.vars()}
    assert "g" in ctx_f_names, ctx_f_names
    assert "f" in ctx_g_names, ctx_g_names


def test_cosynthesis_produces_welltyped_group():
    """End-to-end: both holes are filled and the resulting mutual program type
    checks. The weak ``{r >= 0}`` spec converges instantly under enumeration."""
    d = _driver()
    assert d.parse(aeon_code=MUTUAL_HOLES, filename="<t>") == []
    assert d.has_synth()
    d.synth()
    # After synthesis the core program has no remaining holes and type checks.
    assert check_type(d.typing_ctx, d.core, Top())


def test_partition_targets_identifies_mutual_group():
    """The co-synthesis driver groups a mutual block's targets together (one
    group of two), leaving non-mutual targets as singles."""
    from aeon.synthesis.entrypoint import _partition_targets

    d = _driver()
    assert d.parse(aeon_code=MUTUAL_HOLES, filename="<t>") == []
    targets = incomplete_functions_and_holes(d.typing_ctx, d.core)
    singles, groups = _partition_targets(d.core, targets)
    assert singles == []
    assert len(groups) == 1 and len(groups[0]) == 2
    assert {fn.name for fn, _ in groups[0]} == {"f", "g"}


PBE_MUTUAL = """
mutual
  @example(isEven 0 = true)
  @example(isEven 1 = false)
  def isEven (n: {x:Int | x >= 0}) : Bool decreasing_by [n] := ?he;

  @example(isOdd 0 = false)
  @example(isOdd 1 = true)
  def isOdd (n: {x:Int | x >= 0}) : Bool decreasing_by [n] := ?ho;
end
"""


def test_pbe_mutual_cosynthesis_terminates():
    """Regression guard: with an example-driven (PBE) mutual group, candidate
    evaluation must never block on an unfilled sibling hole (siblings are stubbed
    during co-synthesis). The search may or may not converge on this hard
    instance, but it must terminate within budget rather than hang."""
    d = _driver()
    assert d.parse(aeon_code=PBE_MUTUAL, filename="<t>") == []
    assert d.has_synth()
    # Should return (solved or not) without hanging or raising.
    d.synth()
