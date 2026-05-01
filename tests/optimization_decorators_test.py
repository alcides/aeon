from unittest import mock

from aeon.synthesis.entrypoint import (
    _DEFAULT_PROXY_POWER_W,
    _measure_cputime,
    _measure_energy,
    make_evaluators,
    synthesize_holes,
)
from aeon.synthesis.decorators import Goal
from aeon.synthesis.grammar.ge_synthesis import GESynthesizer, create_problem
from aeon.synthesis.identification import incomplete_functions_and_holes, iterate_top_level
from aeon.sugar.ast_helpers import st_top
from aeon.utils.name import Name

from tests.driver import check_and_return_core, check_compile, extract_core


def test_hole_minimize_int():
    code = """
            def year : Int = 2023;
            def minus : (a:Int) -> (b:Int) -> Int = \\x -> \\y -> x - y;
            @minimize_int( year - (synth 7) )
            def synth(a: Int) : Int = (?hole:Int) * a
        """
    core = extract_core(code)
    assert len(list(iterate_top_level(core))) == 3 + 1


def test_eq() -> None:
    aeon_code = """
        def main(args:Int) : Unit =
            x : String = "ola";
            x1 : String = x;
            x2 : String = x;
            z3 : Bool = x1 == x2;
            print z3
"""

    check_compile(aeon_code, st_top)


def _find_goals(metadata):
    for v in metadata.values():
        if isinstance(v, dict) and "goals" in v:
            return v["goals"]
    return []


def test_minimize_cputime_registers_goal():
    source = """
        @minimize_cputime(synth 7)
        def synth (i:Int) : Int = i * (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = _find_goals(metadata)
    assert len(goals) == 1
    assert goals[0].minimize is True
    assert goals[0].kind == "cputime"


def test_minimize_cpu_time_alias_registers_goal():
    source = """
        @minimize_cpu_time(synth 7)
        def synth (i:Int) : Int = i * (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = _find_goals(metadata)
    assert len(goals) == 1
    assert goals[0].minimize is True
    assert goals[0].kind == "cputime"


def test_minimize_energy_registers_goal():
    source = """
        @minimize_energy(synth 7)
        def synth (i:Int) : Int = i * (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = _find_goals(metadata)
    assert len(goals) == 1
    assert goals[0].minimize is True
    assert goals[0].kind == "energy"


def test_cputime_and_other_objective_compose():
    source = """def year : Int = 2023;
        @minimize_int( year - (synth 7) )
        @minimize_cputime(synth 7)
        def synth (i:Int) : Int = i * (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = _find_goals(metadata)
    assert len(goals) == 2
    kinds = sorted(g.kind for g in goals)
    assert kinds == ["cputime", "expression"]


def test_cputime_and_energy_make_two_evaluators_and_minimize_problem():
    source = """
        @minimize_cputime(synth 7)
        @minimize_energy(synth 7)
        def synth (i:Int) : Int = i * (?hole: Int)
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    # Use the metadata's actual Name key (the unbound one used during desugaring)
    # to look up goals; the Name from incomplete_functions_and_holes carries a
    # post-binding id that doesn't match.
    fun_name = next(k for k, v in metadata.items() if isinstance(v, dict) and "goals" in v)
    evaluators = make_evaluators(ectx, fun_name, metadata)
    assert len(evaluators) == 2
    problem = create_problem(
        validate=lambda _t: True,
        evaluate=lambda _t: [0.0, 0.0],
        fun_name=fun_name,
        metadata=metadata,
    )
    assert problem.minimize == [True, True]


def test_measure_cputime_is_nonnegative():
    cheap = _measure_cputime(lambda: None)
    busy = _measure_cputime(lambda: sum(range(200_000)))
    assert cheap >= 0.0
    assert busy >= 0.0


def test_measure_energy_falls_back_to_proxy_without_pyrapl():
    # Force the pyRAPL import to fail and verify we hit the CPU-time proxy.
    with mock.patch.dict("sys.modules", {"pyRAPL": None}):

        def work():
            sum(range(50_000))

        joules = _measure_energy(work)

    assert joules >= 0.0
    assert joules < _DEFAULT_PROXY_POWER_W * 10.0


def test_cputime_synthesis_smoke():
    """Synthesis with a CPU-time objective completes and returns a hole filling."""
    source = """
        @minimize_cputime(synth 7)
        def synth (i:Int) : Int = i * (?hole: Int)
    """
    core_ast_anf, ctx, ectx, metadata = check_and_return_core(source)
    incomplete = incomplete_functions_and_holes(ctx, core_ast_anf)
    mapping = synthesize_holes(ctx, ectx, core_ast_anf, incomplete, metadata, synthesizer=GESynthesizer(), budget=0.25)
    assert len(mapping) == 1


def test_goal_default_kind_is_expression():
    g = Goal(minimize=True, length=1, function=Name("x", 0))
    assert g.kind == "expression"
