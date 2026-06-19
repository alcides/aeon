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


# --- Instrumented semantics + unsat-core refinement (Contata Algorithm 2) ---


def test_instrumented_trace_records_mutual_calls():
    """Instrumented evaluation (Fig. 4) records every Rec-bound call, including
    nested mutual calls, in post order."""
    from aeon.backend.evaluator import eval_with_trace

    src = """
    mutual
      def even (n: {x:Int | x >= 0}) : Bool decreasing_by [n] := if n = 0 then true else odd (n - 1);
      def odd (n: {x:Int | x >= 0}) : Bool decreasing_by [n] := if n = 0 then false else even (n - 1);
    end
    def main (x: Int) : Int := if even 2 then 1 else 0;
    """
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code=src, filename="<t>") == []
    value, trace = eval_with_trace(d.core, d.evaluation_ctx)
    assert value == 1  # even 2 == true
    names = [(n.name, args, res) for (n, args, res) in trace]
    # even(2) -> odd(1) -> even(0); recorded child-first (post order).
    assert ("even", (0,), True) in names
    assert ("odd", (1,), True) in names
    assert ("even", (2,), True) in names
    assert names[-1][0] == "even" and names[-1][1] == (2,)


def test_smt_unsat_core_blames_unspecified_callee():
    """z3 unsat-core refinement (Algorithm 2, lines 11-16): only ``even`` is
    specified; a candidate ``even(n) = if n=0 then T else odd(n-1)`` with ``odd``
    stubbed to ``False`` makes ``even(2)`` wrong. The structure fact
    ``even(2)=odd(1)`` plus the spec ``even(2)=True`` forces ``odd(1)=True``,
    which contradicts the observed ``odd(1)=False`` — so z3 blames ``odd(1)`` and
    the derived obligation propagates the spec to the unspecified callee."""
    from aeon.synthesis.entrypoint import _smt_unsat_core_obligations
    from aeon.utils.name import Name

    even, odd = Name("even", 6), Name("odd", 7)
    spec = [(even, (0,), True), (even, (1,), False), (even, (2,), True)]
    observed = [(odd, (0,), False), (odd, (1,), False)]  # even-on-spec-inputs is pinned
    symbolic = [((even, (1,)), (odd, (0,))), ((even, (2,)), (odd, (1,)))]
    obligations = _smt_unsat_core_obligations(spec, observed, symbolic, {"even", "odd"})
    assert (odd, (1,), True) in [(f, a, o) for f, a, o in obligations]


def test_smt_consistent_no_obligation():
    """When the candidate's observed behaviour is consistent with the spec, z3
    finds the conjunction satisfiable and derives no obligation."""
    from aeon.synthesis.entrypoint import _smt_unsat_core_obligations
    from aeon.utils.name import Name

    even, odd = Name("even", 6), Name("odd", 7)
    spec = [(even, (0,), True), (even, (2,), True)]
    observed = [(odd, (1,), True)]
    symbolic = [((even, (2,)), (odd, (1,)))]
    assert _smt_unsat_core_obligations(spec, observed, symbolic, {"even", "odd"}) == []


# --- Relational / k-safety specs as a co-synthesis oracle (issue #397, item 2) ---

# A complete mutual group plus a *relational* property that relates the two
# functions (``even n = !(odd n)``) — the kind of k-safety spec over several
# functions that cannot be a single function's refinement type. The domain is
# bounded so property-based testing samples small Nats (recursion-friendly).
_EVEN_ODD = """
mutual
  def even (n: {{x:Int | x >= 0}}) : Bool decreasing_by [n] := if n = 0 then true else odd (n - 1)
  def odd (n: {{x:Int | x >= 0}}) : Bool decreasing_by [n] := if n = 0 then {odd_base} else even (n - 1)
end
@property(15)
def complementary (n: {{x:Int | 0 <= x && x < 6}}) : Bool := even n = !(odd n);
"""


def _joint_accepts_complete(odd_base: str) -> bool:
    from aeon.synthesis.entrypoint import _joint_accepts

    d = _driver()
    assert d.parse(aeon_code=_EVEN_ODD.format(odd_base=odd_base), filename="<t>") == []
    # No holes: the program is complete, so fills is empty and the oracle checks
    # the whole program (type check + @example + @property).
    return _joint_accepts(d.typing_ctx, d.evaluation_ctx, d.core, {}, d.metadata, d.constructor_names)


def test_relational_property_accepts_consistent_group():
    """A relational @property over the group is part of the acceptance oracle:
    a correct even/odd satisfies ``even n = !(odd n)``."""
    assert _joint_accepts_complete("false") is True


def test_relational_property_rejects_inconsistent_group():
    """The same relational property rejects an inconsistent pair (odd's base case
    flipped), even though each function type checks in isolation."""
    assert _joint_accepts_complete("true") is False


def test_cosynthesis_satisfies_relational_property():
    """End-to-end: co-synthesize a mutual group under a relational property that
    the trivial assignment satisfies (``f n = g n``); the synthesized group both
    type checks and passes the property."""
    src = """
    mutual
      def f (n: {x:Int | x >= 0}) : {r:Int | r >= 0} decreasing_by [n] := ?hf
      def g (n: {x:Int | x >= 0}) : {r:Int | r >= 0} decreasing_by [n] := ?hg
    end
    @property(10)
    def agree (n: {x:Int | 0 <= x && x < 6}) : Bool := f n = g n;
    """
    d = _driver()
    assert d.parse(aeon_code=src, filename="<t>") == []
    assert d.has_synth()
    d.synth()
    from aeon.synthesis.pbt.runner import run_properties

    assert check_type(d.typing_ctx, d.core, Top())
    results = run_properties(d.typing_ctx, d.evaluation_ctx, d.core, d.metadata, constructor_names=d.constructor_names)
    assert results and all(r.passed for r in results)
