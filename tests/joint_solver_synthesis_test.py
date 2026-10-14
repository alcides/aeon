"""Shared solver obligations couple all unknowns before fitness evaluation."""

import pytest

from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.modules.smt_synthesizer import SMTSynthesizer
from aeon.synthesis.modules.sygus import SygusSynthesizer
from tests.joint_hole_synthesis_test import parse, solve, fill


@pytest.fixture(params=[SMTSynthesizer, SygusSynthesizer])
def backend(request):
    if request.param is SygusSynthesizer:
        pytest.importorskip("cvc5")
    return request.param()


@pytest.mark.parametrize(
    "source",
    [
        "def x : {v:Int | v > 0} := ?hx; def y : {v:Int | v = x + 1} := ?hy;",
        "def f(x:Int) : {v:Int | v = x + 1} := ?hf; def g(x:Int) : {v:Int | v = f x + 1} := ?hg;",
        "@example(f 0 + g 0 = 3) def f(x:Int):Int := ?hf; def g(x:Int):Int := ?hg;",
        "def n : {v:Int | v = 2} := ?hn; def b(x:Int):{v:Bool | v = (x < 0)} := ?hb;",
        "def n : {v:Int | v = 2} := ?hn; def r : {v:Float | v = 1.5} := ?hr;",
        "def f(x:Int):Int := if ?hc then ?ht else ?he;",
        "def f : (x:Int) -> {v:Int | v = x + 1} := ?hf; def n:{v:Int | v = 2} := ?hn;",
        "def f(x:Int)(y:Int):{v:Int | v = x - y} := ?hf; def n:Int := ?hn;",
    ],
)
def test_complete_joint_solution(backend, source):
    driver = parse(source)
    mapping = solve(driver, backend, budget=5)
    assert len(mapping) >= 2
    fill(driver, mapping)


def test_unsatisfiable_joint_problem_is_reported(backend):
    driver = parse("def x : {v:Int | v > 0 && v < 0} := ?hx; def y:Int := ?hy;")
    with pytest.raises(SynthesisNotSuccessful):
        solve(driver, backend, budget=1)


def test_unsupported_joint_type_is_reported(backend):
    driver = parse("def x:String := ?hx; def y:Int := ?hy;")
    with pytest.raises(SynthesisNotSuccessful, match="cannot translate type"):
        solve(driver, backend, budget=1)


def test_relational_example_is_satisfied_at_runtime(backend):
    from aeon.backend.evaluator import eval as aeon_eval
    from aeon.core.terms import Application, Literal, Var
    from aeon.core.types import t_int
    from aeon.synthesis.fitness_eval import set_program_tail
    from aeon.synthesis.identification import iterate_top_level

    driver = parse("@example(f 0 + g 0 = 37) def f(x:Int):Int := ?hf; def g(x:Int):Int := ?hg;")
    completed = fill(driver, solve(driver, backend, budget=5))
    names = {r.var_name.name: r.var_name for r in iterate_top_level(completed)}
    values = [
        aeon_eval(set_program_tail(completed, Application(Var(names[n]), Literal(0, t_int))), driver.evaluation_ctx)
        for n in ("f", "g")
    ]
    assert sum(values) == 37


def test_universal_relational_property_is_satisfied(backend):
    from aeon.backend.evaluator import eval as aeon_eval
    from aeon.core.terms import Application, Literal, Var
    from aeon.core.types import t_int
    from aeon.synthesis.fitness_eval import set_program_tail
    from aeon.synthesis.identification import iterate_top_level

    driver = parse(
        "def f(x:Int):Int := ?hf; def g(x:Int):Int := ?hg; @property(4) def related(x:Int):Bool := f x + g x = x + 7;"
    )
    completed = fill(driver, solve(driver, backend, budget=5))
    name = next(r.var_name for r in iterate_top_level(completed) if r.var_name.name == "related")
    for value in (-1000, -1, 0, 19, 2000):
        assert (
            aeon_eval(set_program_tail(completed, Application(Var(name), Literal(value, t_int))), driver.evaluation_ctx)
            is True
        )


def test_native_property_is_rejected_explicitly(backend):
    driver = parse(
        'def f(x:Int):Int := ?hf; def g(x:Int):Int := ?hg; @property(4) def related(x:Int):Bool := native "True";'
    )
    with pytest.raises(SynthesisNotSuccessful, match="cannot translate.*native"):
        solve(driver, backend, budget=1)


def test_invalid_complete_solver_result_never_reaches_fitness(backend, monkeypatch):
    from aeon.core.terms import Hole
    from aeon.synthesis.joint import JointCandidate
    from aeon.utils.name import Name
    from aeon.synthesis.modules.sygus import solver as cvc_solver
    from aeon.synthesis import solver_z3

    module = solver_z3 if isinstance(backend, SMTSynthesizer) else cvc_solver
    name = "solve_joint_z3" if module is solver_z3 else "solve_joint_cvc5"
    monkeypatch.setattr(module, name, lambda *args: JointCandidate((Hole(Name("open", 1)),)))

    def must_not_evaluate(candidate):
        raise AssertionError("Fitness ran on an invalid assignment")

    with pytest.raises(SynthesisNotSuccessful, match="failed validation"):
        backend.synthesize_joint(
            (),
            lambda candidate: False,
            must_not_evaluate,
            Name("joint", 0),
            {Name("joint", 0): {"solver_problem": None, "goals": [1]}},
            1,
        )


@pytest.mark.parametrize("solver_name", ["z3", "cvc5"])
def test_all_symbols_share_one_query(solver_name, monkeypatch):
    from collections import Counter
    from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt
    from aeon.core.types import t_int
    from aeon.synthesis.solver_problem import SolverProblem, SolverHole, SolverClause
    from aeon.utils.name import Name
    from aeon.synthesis import solver_z3
    from aeon.synthesis.modules.sygus import solver as cvc_solver

    symbols = [Name("first", 100), Name("second", 101)]
    calls = Counter()
    if solver_name == "z3":
        module, solve_problem = solver_z3.z3, solver_z3.solve_joint_z3
    else:
        module, solve_problem = pytest.importorskip("cvc5"), cvc_solver._solve_joint_cvc5
    original = module.Solver

    class Instrument:
        def __init__(self):
            calls["Solver"] += 1
            self.solver = original()

        def __getattr__(self, name):
            attribute = getattr(self.solver, name)
            if name not in ("check", "checkSynth", "synthFun", "getSynthSolutions"):
                return attribute

            def invoke(*args, **kwargs):
                calls[name] += 1
                return attribute(*args, **kwargs)

            return invoke

    monkeypatch.setattr(module, "Solver", Instrument)
    total = LiquidApp(Name("+", 0), [LiquidApp(symbol, [LiquidLiteralInt(0)]) for symbol in symbols])
    problem = SolverProblem(
        tuple(SolverHole(n, n, (), (), t_int) for n in symbols),
        (SolverClause((), LiquidLiteralBool(True), LiquidApp(Name("==", 0), [total, LiquidLiteralInt(37)])),),
    )
    assert len(solve_problem(problem, 1000).terms) == 2
    assert calls["Solver"] == 1
    assert calls["check" if solver_name == "z3" else "checkSynth"] == 1
    if solver_name == "cvc5":
        assert calls["synthFun"] == 2
        assert calls["getSynthSolutions"] == 1
