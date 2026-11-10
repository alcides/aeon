"""Eager/lazy expansion preserves productions and defers unrequested proofs."""

from time import monotonic

import pytest

from aeon.compilation.session import CompilationSession
from aeon.core.terms import Application, Literal, Var
from aeon.core.types import AbstractionType, TypeConstructor, t_int, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.modules.tdsyn import actions, synthesizer as module
from aeon.synthesis.modules.tdsyn.constraints import deadline
from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches
from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer, _rename_subgoals
from aeon.synthesis.modules.tdsyn.worklist import PartialAST, fresh_hole
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.ctx_helpers import built_std_context
from aeon.utils.name import Name
from tests.synthesis_specifications_test import solve
from tests.tdsyn_relations_test import MASK


@pytest.fixture(autouse=True)
def session():
    with CompilationSession().activate():
        clear_tdsyn_caches()
        yield


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
@pytest.mark.parametrize("backend", ["tdsyn", "tdsyn_enumerative", "tdsyn_backward", "tdsyn_random"])
def test_expansion_flag_reaches_the_backend(expansion, backend, monkeypatch):
    from aeon.__main__ import parse_arguments

    monkeypatch.setattr("sys.argv", ["aeon", "--tdsyn-expansion", expansion, "-s", backend, "example.ae"])
    args = parse_arguments()
    assert make_synthesizer(args.synthesizer, tdsyn_expansion=args.tdsyn_expansion).expansion == expansion


def test_eager_is_default_and_invalid_modes_are_rejected(monkeypatch):
    from aeon.__main__ import parse_arguments

    monkeypatch.setattr("sys.argv", ["aeon", "example.ae"])
    assert parse_arguments().tdsyn_expansion == TDSynSynthesizer().expansion == "eager"
    monkeypatch.setattr("sys.argv", ["aeon", "--tdsyn-expansion", "invalid", "example.ae"])
    with pytest.raises(SystemExit):
        parse_arguments()
    with pytest.raises(ValueError, match="expansion mode"):
        TDSynSynthesizer(expansion="invalid")


def test_lazy_checks_only_the_requested_productions(monkeypatch):
    checked = []

    def feasible(hole, term, children, *args):
        checked.append(term)
        return True

    monkeypatch.setattr(actions, "candidate_feasible", feasible)
    term, hole = fresh_hole(t_int, built_std_context())
    partial = PartialAST(term, [hole], 0)
    backend = TDSynSynthesizer(direction="backward", expansion="lazy")
    stream = backend._iter_expansions(partial, hole, lambda _: True)
    assert checked == []
    assert next(stream).term == Literal(-2, t_int)
    assert checked == [Literal(-2, t_int)]
    assert next(stream).term == Literal(-1, t_int)
    assert checked == [Literal(-2, t_int), Literal(-1, t_int)]
    stream.close()
    checked.clear()
    backend._expand_hole(partial, hole, lambda _: True)
    assert len(checked) == 13


@pytest.mark.parametrize("direction", ["both", "backward"])
def test_exhausting_lazy_expansion_preserves_eager_productions(direction):
    ctx = built_std_context().with_var(Name("x", 0), t_int)
    ctx = ctx.with_var(Name("f", 0), AbstractionType(Name("n", 0), t_int, t_int))
    term, hole = fresh_hole(t_int, ctx)
    partial = PartialAST(term, [hole], 0)
    backend = TDSynSynthesizer(direction=direction)

    def skip(name):
        return name.name not in {"x", "f"}

    def normalized(candidates):
        return [str(_rename_subgoals(candidate.term, Name("test", 0))) for candidate in candidates]

    assert normalized(backend._expand_hole(partial, hole, skip)) == normalized(
        backend._iter_expansions(partial, hole, skip)
    )


def test_lazy_scheduler_explores_a_child_then_resumes_its_siblings(monkeypatch):
    events = []
    goal = TypeConstructor(Name("Box", 0))
    answer = Var(Name("answer", 0))

    def productions(hole, skip, rng=None, **kwargs):
        events.append("child")
        term, child = fresh_hole(goal, hole.context)
        yield Application(Var(Name("grow", 0)), term), [child]
        events.append("sibling")
        yield answer, []

    monkeypatch.setattr(module, "iter_backward_candidates", productions)
    monkeypatch.setattr(module, "is_constructor_term", lambda term: isinstance(term, Application))
    backend = TDSynSynthesizer(direction="backward", expansion="lazy")
    result = backend.synthesize(
        TypingContext(),
        goal,
        lambda term: term == answer,
        lambda _: [],
        Name("f", 0),
        {},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert result == answer
    # Eager consumption would visit the sibling before exploring the child.
    # Unfair depth-first consumption would never return to the sibling.
    assert events == ["child", "child", "sibling"]


def test_lazy_expansion_observes_the_search_deadline(monkeypatch):
    def forbidden(*args, **kwargs):
        pytest.fail("An expired search requested another production")
        yield

    monkeypatch.setattr(module, "iter_backward_candidates", forbidden)
    term, hole = fresh_hole(t_int, TypingContext())
    token = deadline.set(monotonic() - 1)
    try:
        assert (
            list(
                TDSynSynthesizer(expansion="lazy")._iter_expansions(PartialAST(term, [hole], 0), hole, lambda _: False)
            )
            == []
        )
    finally:
        deadline.reset(token)


def test_lazy_random_walk_restarts_after_a_rejected_completion(monkeypatch):
    attempts = []

    def proposals(self, *args):
        value = len(attempts) + 1
        attempts.append(value)
        yield PartialAST(Literal(value, t_int), [], 0)
        pytest.fail("A lazy walk eagerly requested another sibling after its completion")

    monkeypatch.setattr(TDSynSynthesizer, "_walk_expansions", proposals)
    result = TDSynSynthesizer(mode="random", expansion="lazy").synthesize(
        TypingContext(),
        t_int,
        lambda term: term == Literal(2, t_int),
        lambda _: [],
        Name("f", 0),
        {},
        budget=2,
        ui=SilentSynthesisUI(),
    )
    assert result == Literal(2, t_int) and attempts == [1, 2]


@pytest.mark.parametrize("backend", ["tdsyn_enumerative", "tdsyn_backward", "tdsyn_random"])
@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_modes_preserve_relational_constraints_through_the_driver(backend, expansion):
    driver = AeonDriver(AeonConfig(backend, SilentSynthesisUI(), 10, tdsyn_expansion=expansion))
    source = (
        MASK
        + """
        def main(u:Int):{m:Mask{|fun w => fun rest => w + rest <= 1|} |
            Mask.count m = 3 && Mask.weight m = 1} := ?answer;
    """
    )
    assert not list(driver.parse(aeon_code=source))
    assert driver.has_synth()
    driver.synth()
    with driver.session.activate():
        assert check_type(driver.typing_ctx, driver.core, top)
    value, decisions = driver.run(), []
    while value[0] == "Mask_cons":
        _, value, used = value
        decisions.append(used)
    assert value == ("Mask_empty",) and len(decisions) == 3 and sum(decisions) == 1


@pytest.mark.parametrize("expansion", ["eager", "lazy"])
def test_lazy_and_eager_keep_searching_for_objectives(expansion):
    backend = TDSynSynthesizer(direction="backward", expansion=expansion)
    solve(
        "@minimize_int(f 0) @maximize_int(f 0) def f(x:Int):{v:Int | v >= 0 && v <= 1} := ?body;",
        backend,
        budget=0.5,
    )
    assert {tuple(scores) for scores, _ in backend.pareto_front} == {(0.0, 0.0), (1.0, 1.0)}
