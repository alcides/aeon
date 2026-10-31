"""CNF contracts and exact Boolean synthesis, checked independently of selectors."""

from itertools import product

import pytest
import z3

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidVar
from aeon.core.terms import Application, If, Let, Literal, Var
from aeon.core.types import t_bool, t_int
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import InvalidIndividualException, SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.bounded_cnf import CNFError, check_program, normalize
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import iterate_top_level
from aeon.synthesis.joint import HoleSpec, JointCandidate, JointSynthesizer
from aeon.synthesis.modules.boolean_bounded import BooleanBoundedSynthesizer, BoundedBooleanFailure
from aeon.synthesis.modules.random_search import RandomSearchSynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_family, SynthesizerFamily
from aeon.synthesis.solver_problem import SolverClause, SolverHole, SolverProblem
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name
from tests.joint_hole_synthesis_test import parse, solve, fill


def app(op, *args):
    result = Var(Name(op, 0))
    for arg in args:
        result = Application(result, arg)
    return result


def call(driver, completed, name, *args):
    names = {r.var_name.name: r.var_name for r in iterate_top_level(completed)}
    term = Var(names[name])
    for arg in args:
        term = Application(term, Literal(arg, t_bool))
    return aeon_eval(set_program_tail(completed, term), driver.evaluation_ctx)


def run(source):
    driver = parse(source)
    backend = BooleanBoundedSynthesizer()
    completed = fill(driver, solve(driver, backend, budget=5))
    assert check_program(completed, driver.metadata)
    assert backend.report.status == "solved"
    return driver, completed, backend


@pytest.mark.parametrize(
    "bound,wanted,feasible", [(0, True, True), (0, False, False), (1, False, True), (1, True, True)]
)
def test_nullary_constants(bound, wanted, feasible):
    source = f"@bounded_cnf({bound}) def f:{{r:Bool | r = {str(wanted).lower()}}} := ?h;"
    if feasible:
        driver, completed, _ = run(source)
        assert call(driver, completed, "f") is wanted
    else:
        with pytest.raises(BoundedBooleanFailure) as exc:
            run(source)
        assert exc.value.category == "bounded_unsat"


@pytest.mark.parametrize(
    "expression,k,expected",
    [
        ("x", 1, lambda x, y: x),
        ("!x", 1, lambda x, y: not x),
        ("x || y", 1, lambda x, y: x or y),
        ("x && y", 2, lambda x, y: x and y),
        ("x != y", 2, lambda x, y: x != y),
    ],
)
def test_boolean_functions(expression, k, expected):
    driver, completed, backend = run(f"@bounded_cnf({k}) def f(x:Bool)(y:Bool):{{r:Bool | r = ({expression})}} := ?h;")
    for x, y in product([False, True], repeat=2):
        assert call(driver, completed, "f", x, y) is expected(x, y)
    assert backend.report.counterexamples > 0
    assert backend.report.iterations == backend.report.counterexamples + 1


def test_xor_boundary_and_inconsistent_total_contract():
    for refinement in ("r = (x != y)", "r && !r"):
        with pytest.raises(BoundedBooleanFailure) as exc:
            run(f"@bounded_cnf(1) def f(x:Bool)(y:Bool):{{r:Bool | {refinement}}} := ?h;")
        assert exc.value.category == "bounded_unsat"


def test_full_function_hole_and_captured_local():
    for source in (
        "@bounded_cnf(1) def f:(x:Bool) -> {r:Bool | r = !x} := ?h;",
        "@bounded_cnf(1) def f(x:Bool):{r:Bool | r = !x} := let captured := x in (?h : {r:Bool | r = !captured});",
    ):
        driver, completed, _ = run(source)
        assert call(driver, completed, "f", False) is True
        assert call(driver, completed, "f", True) is False


@pytest.mark.parametrize("domain", ["x", "false"])
def test_declared_domains(domain):
    driver, completed, _ = run(
        f"@bounded_cnf(0) def f(x:{{v:Bool | {domain.replace('x', 'v')}}}):{{r:Bool | r = x}} := ?h;"
    )
    assert call(driver, completed, "f", True) is True


def test_single_hole_property_is_universal_not_sampled():
    driver, completed, _ = run("""
        @bounded_cnf(1) def f(x:Bool):Bool := ?h;
        @property(1) def law(x:Bool):Bool := f x = !x;
    """)
    for x in (False, True):
        assert call(driver, completed, "law", x) is True


def test_coupled_outputs_repeated_and_nested_calls():
    driver, completed, _ = run("""
        @bounded_cnf(1) def f(x:Bool):Bool := ?hf;
        @bounded_cnf(1) def g(x:Bool):Bool := ?hg;
        @property(1) def law(x:Bool):Bool :=
            (f x != g x) && (f (f x) = f x) && (f (!x) = !f x);
    """)
    for x in (False, True):
        assert call(driver, completed, "law", x) is True


def test_relational_examples():
    driver, completed, _ = run("""
        @bounded_cnf(0)
        @example(f true != g false)
        def f(x:Bool):Bool := ?hf;
        @bounded_cnf(1) def g(x:Bool):Bool := ?hg;
    """)
    assert call(driver, completed, "f", True) != call(driver, completed, "g", False)


def test_explicit_partial_relation_does_not_leak_witnesses():
    driver, completed, _ = run("""
        def relation(x:Bool)(witness:Bool):Bool := x && !witness;
        @bounded_cnf(1) def f(x:Bool):Bool := ?h;
        @property(1) def law(x:Bool)(witness:Bool):Bool :=
            relation x witness --> relation x (f x);
    """)
    for x, witness in product([False, True], repeat=2):
        assert call(driver, completed, "law", x, witness) is True
    # A total contract must fail on x=false; it may not infer a feasibility domain.
    with pytest.raises(BoundedBooleanFailure) as exc:
        run("@bounded_cnf(1) def f(x:Bool):{r:Bool | x && !r} := ?h;")
    assert exc.value.category == "bounded_unsat"


def test_quantified_witness_is_not_an_input():
    with pytest.raises(BoundedBooleanFailure) as exc:
        run("""
            @bounded_cnf(2) def f(x:Bool):Bool := ?h;
            @property(1) def impossible(x:Bool)(witness:Bool):Bool := f x = witness;
        """)
    assert exc.value.category == "bounded_unsat"


def test_normalization_and_name_identity():
    x, same_spelling = Name("x", 10), Name("x", 11)
    v, other = Var(x), Var(same_spelling)
    assert normalize(Literal(True, t_bool), set()) == ()
    assert normalize(Literal(False, t_bool), set()) == (frozenset(),)
    assert len(normalize(app("&&", v, v), {x})) == 1
    assert len(normalize(app("||", v, v), {x})) == 1
    assert normalize(app("||", v, app("!", v)), {x}) == ()
    assert len(normalize(app("||", v, app("!", other)), {x, same_spelling})) == 1
    assert normalize(app("&&", Literal(False, t_bool), v), {x}) == (frozenset(),)
    assert normalize(app("&&", Literal(True, t_bool), app("!", app("!", v))), {x}) == normalize(v, {x})
    alias = Name("alias", 12)
    assert normalize(Let(alias, v, Let(x, other, Var(alias))), {x, same_spelling}) == normalize(v, {x})
    for term in (other, If(v, v, v), app("helper", v), app("!", app("&&", v, v)), app("||", v, app("&&", v, v))):
        with pytest.raises(CNFError):
            normalize(term, {x})
    # Invalid syntax cannot hide behind a true/false constant.
    with pytest.raises(CNFError):
        normalize(app("||", Literal(True, t_bool), app("helper", v)), {x})
    with pytest.raises(CNFError, match="limit"):
        normalize(v, {x}, max_nodes=0)


@pytest.mark.parametrize(
    "annotation",
    [
        "@bounded_cnf",
        "@bounded_cnf(-1)",
        "@bounded_cnf(true)",
        "@bounded_cnf(1, 2)",
        "@bounded_cnf(1.0)",
        "@bounded_cnf(1) @bounded_cnf(2)",
    ],
)
def test_bad_decorator_is_an_error(annotation):
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    errors = driver.parse(aeon_code=f"{annotation} def f:Bool := ?h;")
    assert errors
    assert "bounded_cnf" in str(errors)


@pytest.mark.parametrize(
    "source",
    [
        "def f(x:Bool):Bool := ?h;",
        "@bounded_cnf(1) def f(x:Int):Bool := ?h;",
        "@bounded_cnf(1) def f(x:Bool):Int := ?h;",
        "@bounded_cnf(1) def f(g:(x:Bool) -> Bool):Bool := ?h;",
        "@bounded_cnf(1) def f(1 x:Bool):Bool := ?h;",
        '@bounded_cnf(1) def f(x:Bool):Bool := ?h; @property(1) def law(x:Bool):Bool := native "True";',
        "@bounded_cnf(1) def f(x:Bool):Bool := if ?h then ?g else false;",
    ],
)
def test_unsupported_programs_fail_clearly(source):
    with pytest.raises(UnsupportedSynthesisGoal):
        run(source)


def test_shared_gate_rejects_before_scoring_single_and_joint(monkeypatch):
    from aeon.synthesis.api import Synthesizer
    from aeon.synthesis.evaluation_pool import EvaluationPool

    def must_not_run(*args):
        raise AssertionError("invalid candidate reached the fitness worker")

    monkeypatch.setattr(EvaluationPool, "run", must_not_run)

    class Single(Synthesizer):
        def synthesize(self, **kwargs):
            for candidate in (Literal(False, t_bool), Literal(1, t_int)):
                assert not kwargs["validate"](candidate)
                with pytest.raises(InvalidIndividualException):
                    kwargs["evaluate"](candidate)
            return Literal(False, t_bool)

    class Joint(JointSynthesizer):
        def synthesize_joint(self, holes, validate, evaluate, *args):
            bad = JointCandidate(tuple(Literal(False, t_bool) for _ in holes))
            assert not validate(bad)
            with pytest.raises(InvalidIndividualException):
                evaluate(bad)
            return bad

    with pytest.raises(SynthesisNotSuccessful):
        solve(parse("@bounded_cnf(0) def f:Bool := ?h;"), Single())
    assert all(
        value is None
        for value in solve(
            parse("@bounded_cnf(0) def f:Bool := ?h; @bounded_cnf(0) def g:Bool := ?g;"), Joint()
        ).values()
    )


def test_compatible_baseline_respects_zero_clause_bound():
    driver = parse("@bounded_cnf(0) def f:Bool := ?h;")
    completed = fill(driver, solve(driver, RandomSearchSynthesizer(seed=0), budget=1))
    assert check_program(completed, driver.metadata)
    assert call(driver, completed, "f") is True


def test_factory_seed_and_menu(monkeypatch):
    from aeon.lsp.server import SYNTHESIZERS

    monkeypatch.setenv("AEON_SEED", "27")
    backend = make_synthesizer("boolean_bounded")
    assert isinstance(backend, BooleanBoundedSynthesizer) and backend.seed == 27
    assert synthesizer_family("boolean_bounded") is SynthesizerFamily.CONSTRAINT_SOLVING
    assert "boolean_bounded" in SYNTHESIZERS


# Direct adapter tests supply independent Boolean truth tables, not template bits.
def direct_problem(k, truth_table):
    x, y, h, f, symbol = (Name(n, i + 100) for i, n in enumerate(("x", "x", "h", "f", "unknown")))
    params = ((x, t_bool), (y, t_bool))
    unknown = LiquidApp(symbol, [LiquidVar(x), LiquidVar(y)])
    clauses = []
    for inputs, wanted in zip(product([False, True], repeat=2), truth_table):
        premise = LiquidApp(
            Name("&&", 0),
            [LiquidApp(Name("==", 0), [LiquidVar(n), LiquidLiteralBool(v)]) for (n, _), v in zip(params, inputs)],
        )
        clauses.append(SolverClause(params, premise, LiquidApp(Name("==", 0), [unknown, LiquidLiteralBool(wanted)])))
    hole = HoleSpec(h, f, t_bool, TypingContext())
    problem = SolverProblem((SolverHole(h, symbol, params, (), t_bool),), tuple(clauses))
    return (hole,), {f: {"bounded_cnf": k}, Name("joint", 0): {"solver_problem": problem}}, params


def direct(backend, holes, metadata, validate=lambda _: True, evaluate=lambda _: [], budget=5):
    return backend.synthesize_joint(holes, validate, evaluate, Name("joint", 0), metadata, budget, SilentSynthesisUI())


def cnf_outputs(candidate, params):
    # Structural normalization then a truth-table interpreter independent of Z3.
    cnf = normalize(candidate.terms[0], {n for n, _ in params})
    return tuple(
        all(any(dict(zip((n for n, _ in params), values))[name] == sign for name, sign in clause) for clause in cnf)
        for values in product([False, True], repeat=2)
    )


def test_exhaustive_two_input_family_agreement():
    valuations = tuple(product([False, True], repeat=2))
    clauses = [
        tuple(any(sign != 0 and values[i] == (sign == 1) for i, sign in enumerate(signs)) for values in valuations)
        for signs in product([0, 1, -1], repeat=2)
    ]
    for k in (0, 1, 2):
        expressible = {
            tuple(all(c[i] for c in selected) for i in range(4))
            for size in range(k + 1)
            for selected in product(clauses, repeat=size)
        }
        for wanted in product([False, True], repeat=4):
            holes, metadata, params = direct_problem(k, wanted)
            backend = BooleanBoundedSynthesizer()
            if wanted in expressible:
                candidate = direct(backend, holes, metadata)
                assert cnf_outputs(candidate, params) == wanted
            else:
                with pytest.raises(BoundedBooleanFailure) as exc:
                    direct(backend, holes, metadata)
                assert exc.value.category == "bounded_unsat"


def test_failure_categories_and_reset(monkeypatch):
    holes, metadata, _ = direct_problem(1, [True] * 4)
    for backend, budget, category in (
        (BooleanBoundedSynthesizer(), 0, "timeout"),
        (BooleanBoundedSynthesizer(max_selectors=0), 1, "resource_limit"),
        (BooleanBoundedSynthesizer(max_nodes=0), 1, "resource_limit"),
    ):
        with pytest.raises(BoundedBooleanFailure) as exc:
            direct(backend, holes, metadata, budget=budget)
        assert exc.value.category == backend.report.status == category
    backend = BooleanBoundedSynthesizer()

    def must_not_score(_):
        raise AssertionError("fitness reached before validation")

    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(backend, holes, metadata, validate=lambda _: False, evaluate=must_not_score)
    assert exc.value.category == "validation_error"
    first = direct(backend, holes, metadata)
    second = direct(backend, holes, metadata)
    assert first == second and backend.report.counterexamples <= 4
    monkeypatch.setattr(z3.Solver, "check", lambda self: z3.unknown)
    monkeypatch.setattr(z3.Solver, "reason_unknown", lambda self: "injected unknown")
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(backend, holes, metadata)
    assert exc.value.category == "unknown"


def test_completed_program_needs_no_search():
    driver = parse("@bounded_cnf(0) def f:Bool := true;")
    assert solve(driver, BooleanBoundedSynthesizer()) == {}


def test_recursion_is_a_capability_error():
    driver = parse("@bounded_cnf(1) def f(x:Bool):Bool := if x then f false else ?h;")
    with pytest.raises(UnsupportedSynthesisGoal, match="recursive"):
        solve(driver, BooleanBoundedSynthesizer(), budget=1)


def test_no_dependence_on_another_outputs_private_input():
    with pytest.raises(BoundedBooleanFailure) as exc:
        run("""
            @bounded_cnf(1) def f(x:Bool):{r:Bool | r = x} := ?hf;
            @bounded_cnf(1) def g(x:Bool):Bool := ?hg;
            @property(1) def law(left:Bool)(right:Bool):Bool := f left = g right;
        """)
    assert exc.value.category == "bounded_unsat"


def test_optional_objective_is_reported_after_validity():
    driver, completed, _ = run("""
        def cost(x:Bool):Int := if x then 0 else 1;
        @bounded_cnf(1)
        @minimize_int(cost (f true))
        def f(x:Bool):{r:Bool | r = !x} := ?h;
    """)
    assert call(driver, completed, "f", True) is False


def test_annotation_round_trip_and_examples():
    from pathlib import Path
    from aeon.sugar.parser import parse_main_program
    from aeon.utils.pprint import pretty_print_node

    source = "@bounded_cnf(2) def f(x:Bool):Bool := ?h;"
    program = parse_main_program(source, filename="<test>")
    rendered = pretty_print_node(program)
    driver = parse(rendered)
    assert any(entry.get("bounded_cnf") == 2 for entry in driver.metadata.values())
    for path in Path("examples/synthesis/boolean_bounded").glob("*.ae"):
        run(path.read_text())


def test_exhaustive_nullary_joint_relations():
    from aeon.core.liquid import LiquidLiteralInt

    names = [Name("out", 400), Name("out", 401)]
    holes = tuple(HoleSpec(n, n, t_bool, TypingContext()) for n in names)
    schemas = tuple(SolverHole(n, n, (), (), t_bool) for n in names)
    calls = [LiquidApp(n, [LiquidLiteralInt(0)]) for n in names]
    choices = tuple(product([False, True], repeat=2))
    for k in (0, 1):
        for mask in product([False, True], repeat=4):
            relation = LiquidLiteralBool(False)
            for wanted, enabled in zip(choices, mask):
                if enabled:
                    pair = LiquidApp(
                        Name("&&", 0),
                        [LiquidApp(Name("==", 0), [c, LiquidLiteralBool(v)]) for c, v in zip(calls, wanted)],
                    )
                    relation = LiquidApp(Name("||", 0), [relation, pair])
            problem = SolverProblem(schemas, (SolverClause((), LiquidLiteralBool(True), relation),))
            metadata = {n: {"bounded_cnf": k} for n in names} | {Name("joint", 0): {"solver_problem": problem}}
            feasible = any(enabled and (k == 1 or all(values)) for enabled, values in zip(mask, choices))
            if feasible:
                candidate = direct(BooleanBoundedSynthesizer(), holes, metadata)
                values = tuple(normalize(t, set()) == () for t in candidate.terms)
                assert mask[choices.index(values)]
            else:
                with pytest.raises(BoundedBooleanFailure) as exc:
                    direct(BooleanBoundedSynthesizer(), holes, metadata)
                assert exc.value.category == "bounded_unsat"


@pytest.mark.parametrize(
    "phase,reason,category",
    [(1, "injected unknown", "unknown"), (2, "injected unknown", "unknown"), (2, "timeout", "timeout")],
)
def test_solver_failures_are_not_unsat(monkeypatch, phase, reason, category):
    holes, metadata, _ = direct_problem(1, [True] * 4)
    original = z3.Solver.check
    calls = 0

    def check(solver):
        nonlocal calls
        calls += 1
        return z3.unknown if calls == phase else original(solver)

    monkeypatch.setattr(z3.Solver, "check", check)
    monkeypatch.setattr(z3.Solver, "reason_unknown", lambda _: reason)
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(BooleanBoundedSynthesizer(), holes, metadata)
    assert exc.value.category == category


def test_extraction_failure_is_not_unsat(monkeypatch):
    from aeon.synthesis.modules.boolean_bounded import _Template

    holes, metadata, _ = direct_problem(1, [True] * 4)

    def fail(*args):
        raise ValueError("injected extraction failure")

    monkeypatch.setattr(_Template, "extract", fail)
    with pytest.raises(BoundedBooleanFailure) as exc:
        direct(BooleanBoundedSynthesizer(), holes, metadata)
    assert exc.value.category == "validation_error"


def test_unused_opaque_alias_is_not_erased_by_normalization():
    with pytest.raises(CNFError):
        normalize(Let(Name("unused", 9), app("opaque", Literal(True, t_bool)), Literal(True, t_bool)), set())


def test_adapters_without_a_shared_gate_fail_explicitly():
    from aeon.synthesis.api import ProgramSynthesizer, Synthesizer

    with pytest.raises(UnsupportedSynthesisGoal, match="shared candidate-validation"):
        solve(parse("@bounded_cnf(0) def f:Bool := ?h;"), ProgramSynthesizer())
    with pytest.raises(UnsupportedSynthesisGoal, match="joint synthesizer"):
        solve(parse("@bounded_cnf(0) def f:Bool := ?h; @bounded_cnf(0) def g:Bool := ?g;"), Synthesizer())
