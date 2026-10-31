"""Lifted interpretation preserves languages, not just representatives."""

from itertools import product
from pathlib import Path
from time import monotonic

import pytest

from aeon.backend.evaluator import EvaluationContext, eval as evaluate
from aeon.core.substitutions import substitution
from aeon.core.terms import Abstraction, Application, Hole, Let, Literal, Rec, Term, TypeApplication, Var
from aeon.core.types import t_int, t_bool
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import get_holes_info
from aeon.synthesis.modules.arborist import ArboristSynthesizer
from aeon.synthesis.modules.arborist.forest import Forest, scalar_labels, scalar_key
from aeon.synthesis.modules.arborist.interpreter import LiftedInterpreter
from aeon.synthesis.modules.bottom_up import application
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_family, SynthesizerFamily
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name

ROOT = Path(__file__).resolve().parents[1]
A, X, H = Name("acc", 100), Name("element", 101), Name("body", 102)


def forest(*, compress=True):
    labels = scalar_labels(
        [(A, t_int), (X, t_int)], {Name("+", 0), Name("-", 0)}, constants=(1,), operators=("+", "-"), conditionals=False
    )
    return Forest(labels, monotonic() + 20, compress=compress)


def solve(source, backend=None, budget=10):
    d = AeonDriver(AeonConfig("arborist", SilentSynthesisUI(), budget, no_main=True))
    assert not list(d.parse(aeon_code=source))
    d.has_synth()
    backend = backend or ArboristSynthesizer()
    with d.session.activate():
        result = synthesize_holes(
            d.typing_ctx,
            d.evaluation_ctx,
            d.core,
            d.incomplete_functions,
            d.metadata,
            backend,
            budget,
            SilentSynthesisUI(),
        )
        filled = d.core
        for name, body in result.items():
            assert body is not None
            filled = substitution(filled, body, name)
        value = evaluate(set_program_tail(filled, Var(d.incomplete_functions[0][0])), d.evaluation_ctx)
    return value, backend, result


def test_registered_backend():
    assert isinstance(make_synthesizer("arborist"), ArboristSynthesizer)
    assert synthesizer_family("arborist") == SynthesizerFamily.AUTOMATA


def test_classes_split_when_a_new_context_distinguishes_programs():
    f = forest()
    root = f.grammar(t_int, 1)
    first = dict(f.specialize(root, {A: 0, X: 1}))[1]
    terms = set(f.terms(first))
    plus = application(TypeApplication(Var(Name("+", 0)), t_int), (Var(A), Var(X)))
    assert Var(X) in terms and plus in terms
    second = dict(f.specialize(first, {A: 3, X: 2}))
    assert Var(X) in set(f.terms(second[2]))
    assert plus in set(f.terms(second[5]))
    assert plus not in set(f.terms(second[2]))
    assert f.stats.merges > 0


def enumerate_terms(depth):
    """Independent, uncompressed syntax enumeration for the test grammar."""
    atoms = [Var(A), Var(X), Literal(1, t_int)]
    if depth == 0:
        return atoms
    children = enumerate_terms(depth - 1)
    return atoms + [
        application(TypeApplication(Var(Name(op, 0)), t_int), args)
        for op in ("+", "-")
        for args in product(children, repeat=2)
    ]


def fold_sketch(values):
    """A small unrolled fold with a shared callback; ordinary Core evaluation
    provides an oracle independent of the lifted interpreter."""
    function = Name("step", 103)
    result: Term = Literal(0, t_int)
    for value in values:
        result = Application(Application(Var(function), result), Literal(value, t_int))
    return Let(function, Abstraction(A, Abstraction(X, Hole(H))), result)


@pytest.mark.parametrize("depth", [0, 1, 2])
@pytest.mark.parametrize("values", [(1, 2), (2, 1, 3)])
def test_lifted_fold_preserves_exact_exhaustive_solution_languages(depth, values):
    f = forest()
    sketch = fold_sketch(values)
    interpreter = LiftedInterpreter(f, {}, H)
    outputs = {}
    for value, state in interpreter.evaluate(sketch, {}, f.grammar(t_int, depth)):
        outputs.setdefault(value, set()).update(f.terms(state))
    expected = {}
    ectx = EvaluationContext({Name("+", 0): lambda x: lambda y: x + y, Name("-", 0): lambda x: lambda y: x - y})
    for candidate in enumerate_terms(depth):
        value = evaluate(substitution(sketch, candidate, H), ectx)
        expected.setdefault(value, set()).add(candidate)
    assert outputs == expected
    assert any(context[0][1] != 0 for context in interpreter.reachable)


def test_same_program_must_be_used_across_iterations():
    # Two calls of the same constant callback must agree. Resetting the
    # language between calls would spuriously admit differences of +/-1.
    f = Forest(scalar_labels([], set(), constants=(1, 2), operators=(), conditionals=False), monotonic() + 10)
    # Different hole contexts must narrow the same language, even with no vars.
    step = Name("step", 105)
    first = Name("first", 106)
    call = Application(Var(step), Literal(0, t_int))
    difference = application(TypeApplication(Var(Name("-", 0)), t_int), (call, Var(first)))
    sketch = Let(step, Abstraction(A, Hole(H)), Let(first, call, difference))
    outputs = list(LiftedInterpreter(f, {}, H).evaluate(sketch, {}, f.grammar(t_int, 0)))
    assert {value for value, _ in outputs} == {0}
    assert all(f.count(state) == 1 for _, state in outputs)


def test_compression_reduces_intermediate_transition_products():
    counts = []
    languages = []
    for compress in (True, False):
        f = forest(compress=compress)
        results = f.specialize(f.grammar(t_int, 2), {A: 0, X: 1})
        grouped = {}
        for value, state in results:
            grouped.setdefault(value, set()).update(f.terms(state))
        languages.append(grouped)
        counts.append(f.stats.transitions)
        if compress:
            assert f.stats.merges > 0
    assert languages[0] == languages[1]
    assert counts[0] < counts[1] / 2


def test_end_to_end_local_lambda():
    f, backend, _ = solve((ROOT / "examples/synthesis/arborist/local.ae").read_text())
    assert [f(x) for x in (2, 3, 4, 5)] == [5, 10, 17, 26]
    assert backend.stats.merges > 0


def test_end_to_end_fold_accumulator_contexts():
    f, backend, _ = solve((ROOT / "examples/synthesis/arborist/fold.ae").read_text())
    assert [f(n) for n in range(8)] == [n * (n + 1) // 2 for n in range(8)]
    assert backend.stats.merges > 0 and len(backend.reachable) > 5


def test_refinement_rejection_keeps_other_example_equivalent_terms():
    # At x=0, literal 1 and x+1 agree; only the latter meets the contract.
    f, backend, _ = solve("@example(f 0 = 1)\ndef f (x:Int) : {r:Int | r = x + 1} := ?body;")
    assert f(7) == 8
    assert backend.stats.validated > 1


def test_budget_and_missing_examples_are_controlled():
    with pytest.raises(SynthesisNotSuccessful, match="budget"):
        solve("@example(f 0 = 1)\ndef f (x:Int) : Int := ?body;", budget=0)
    with pytest.raises(UnsupportedSynthesisGoal, match="@example"):
        solve("def f (x:Int) : Int := ?body;")


def test_observation_identity_distinguishes_bool_from_int():
    assert scalar_key(True) != scalar_key(1)
    f = forest()
    assert f.grammar(t_int, 0) != f.grammar(t_bool, 0)


def test_bool_synthesis_and_local_shadowing():
    f, _, _ = solve("@example(f true = false)\n@example(f false = true)\ndef f (x:Bool) : Bool := ?body;")
    assert f(True) is False and f(False) is True
    f, _, _ = solve("""@example(f 1 = 7)
        @example(f 2 = 8)
        def f (x:Int) : Int := let y := x + 1 in let x := 5 in ?body;""")
    assert f(10) == 16


def test_fixed_local_closure_keeps_its_lexical_bindings():
    f, _, _ = solve("""def apply (f:(z:Int) -> Int) (z:Int) : Int := f z;
        @example(f 1 = 3)
        @example(f 2 = 5)
        @example(f 3 = 7)
        def f (x:Int) : Int :=
            let y := x + 1 in
            let callback : (z:Int) -> Int := fun z => ?body in
            let y := 0 in apply callback x;""")
    assert f(5) == 11


def test_unit_shadow_bindings_are_administrative():
    f, _, _ = solve("""@example(f 2 = 4)
        @example(f 3 = 5)
        def f (x:Int) : Int := let y := x in let x : Unit := unit in ?body;""")
    assert f(8) == 10


def test_rejects_additional_objectives_multiple_holes_and_opaque_values():
    with pytest.raises(UnsupportedSynthesisGoal, match="optimization"):
        solve("@minimize_int(f 0)\n@example(f 0 = 1)\ndef f (x:Int) : Int := ?body;")
    with pytest.raises(UnsupportedSynthesisGoal, match="one expression hole"):
        solve("@example(f 0 = 1)\ndef f (x:Int) : Int := (?a : Int) + (?b : Int);")
    with pytest.raises(UnsupportedSynthesisGoal, match="Int or Bool"):
        scalar_key(1.0)
    with pytest.raises(SynthesisNotSuccessful, match="integer limit"):
        scalar_key(1 << 4096)


def test_state_and_execution_limits_report_exhaustion():
    source = (ROOT / "examples/synthesis/arborist/fold.ae").read_text()
    with pytest.raises(SynthesisNotSuccessful, match="state limit"):
        solve(source, ArboristSynthesizer(max_states=1))
    with pytest.raises(SynthesisNotSuccessful, match="step limit"):
        solve(source, ArboristSynthesizer(max_steps=1))


def int_list(*values, prefix="IntList"):
    result = (prefix + "_nil",)
    for value in reversed(values):
        result = (prefix + "_cons", value, result)
    return result


def test_paper_list_fold_synthesizes_and_preserves_both_paper_programs():
    source = (ROOT / "examples/synthesis/arborist/list_fold.ae").read_text()
    fun, _, _ = solve(source)
    assert fun(int_list(1, 2, 4)) == 7

    driver = AeonDriver(AeonConfig("arborist", SilentSynthesisUI(), 10, no_main=True))
    assert not list(driver.parse(aeon_code=source))
    driver.has_synth()
    with driver.session.activate():
        function, (hole,) = driver.incomplete_functions[0]
        _, ctx = get_holes_info(driver.typing_ctx, driver.core, t_int, driver.incomplete_functions)[hole]
        names = {n.name: n for n, _ in ctx.vars() if n.name in ("acc", "element")}
        definitions = {}
        current = driver.core
        while isinstance(current, (Let, Rec)):
            definitions[current.var_name] = current.var_value
            if current.var_name == function:
                break
            current = current.body
        labels = scalar_labels(
            [(n, t_int) for n in names.values()],
            {Name("+", 0), Name("*", 0)},
            constants=(1, 2),
            operators=("+", "*"),
            conditionals=False,
        )
        f = Forest(labels, monotonic() + 10)
        interpreter = LiftedInterpreter(f, definitions, hole)
        root = f.grammar(t_int, 2)
        survivors = [s for v, s in interpreter.run(function, [int_list(1, 2, 4)], root) if v == 7]
        terms = set(f.terms(f.union(survivors)))
        plus = TypeApplication(Var(Name("+", 0)), t_int)
        times = TypeApplication(Var(Name("*", 0)), t_int)
        p1 = application(plus, (Var(names["acc"]), Var(names["element"])))
        p2 = application(plus, (application(times, (Var(names["acc"]), Literal(2, t_int))), Literal(1, t_int)))
        assert p1 in terms and p2 in terms
        # Independently execute both callbacks with the ordinary Aeon fold.
        fold_name = next(n for n in definitions if n.name == "fold_left")
        for candidate in (p1, p2):
            filled = substitution(driver.core, candidate, hole)
            fold = evaluate(set_program_tail(filled, Var(fold_name)), driver.evaluation_ctx)
            callback = evaluate(
                Abstraction(names["acc"], Abstraction(names["element"], candidate)), driver.evaluation_ctx
            )
            footprint = []

            def step(acc):
                def apply(element):
                    result = callback(acc)(element)
                    footprint.append((acc, element, result))
                    return result

                return apply

            assert fold(step)(0)(int_list(1, 2, 4)) == 7
            assert footprint == [(0, 1, 1), (1, 2, 3), (3, 4, 7)]
        # A second input separates the paper's observationally equal bodies.
        second = [s for v, s in interpreter.run(function, [int_list(4)], f.union(survivors)) if v == 4]
        terms = set(f.terms(f.union(second)))
        assert p1 in terms and p2 not in terms


def test_list_sum_synthesizes_and_generalizes_to_unseen_lists():
    source = (ROOT / "examples/synthesis/arborist/list_sum.ae").read_text()
    fun, backend, _ = solve(source)
    for values in ((), (0,), (-3, 8), (4, 2, 1), (10, -2, 7, 0), (1, 1, 1, 1, 1)):
        assert fun(int_list(*values)) == sum(values)
    assert backend.stats.merges > 0


def test_list_fold_order_is_left_to_right():
    source = (ROOT / "examples/synthesis/arborist/list_fold.ae").read_text().replace("= 7)", "= 124)")
    source = source.replace(
        "def fold_example",
        "@example(fold_example (.cons 4 (.cons 2 (.cons 1 .nil))) = 421)\ndef fold_example",
    )
    fun, _, _ = solve(source, ArboristSynthesizer(constants=(0, 1, 2, 10), operators=("+", "*"), conditionals=False))
    assert fun(int_list(3, 1)) == 31
    assert fun(int_list()) == 0


def test_inductive_support_uses_declarations_including_constructor_order():
    # Neither the datatype name nor its constructors/order are list-specific.
    source = """inductive Chain a
        | link (head:a) (tail:(Chain a)) : (Chain a)
        | end : (Chain a)
        def walk (f:(acc:Int) -> (value:Int) -> Int) (acc:Int) (xs:(Chain Int)) : Int :=
            match xs with | .end => acc | .link head tail => walk f (f acc head) tail;
        @example(total (.link 2 (.link 5 .end)) = 7)
        @example(total (.link 4 .end) = 4)
        @example(total .end = 0)
        def total (xs:(Chain Int)) : Int := walk (fun acc => fun value => ?body) 0 xs;"""
    fun, _, _ = solve(source)
    assert fun(("Chain_link", 3, ("Chain_link", 6, ("Chain_end",)))) == 9


def test_constructor_creation_inside_the_sketch_and_scalar_inputs():
    source = """inductive Box | box (x:Int) : Box
        def unpack (b:Box) : Int := match b with | .box x => x;
        @example(f 2 = 3)
        @example(f 5 = 6)
        def f (x:Int) : Int :=
            let b : Box := .box (x + 1) in
            let x : Unit := unit in
            let y := unpack b in ?body;"""
    fun, _, _ = solve(source)
    assert fun(11) == 12


def test_native_and_shadowed_constructor_names_do_not_gain_inductive_semantics():
    for source in (
        """inductive Box | box (x:Int) : Box
        def Box_box (x:Int) : Int := x + 3;
        @example(f 2 = 5)
        @example(f 4 = 7)
        def f (x:Int) : Int := let y := Box_box x in let x : Unit := unit in ?body;""",
        """inductive Box | box (x:Int) : Box
        def Box_rec (x:Int) : Int := x + 3;
        @example(f 2 = 5)
        @example(f 4 = 7)
        def f (x:Int) : Int := let y := Box_rec x in let x : Unit := unit in ?body;""",
    ):
        fun, _, _ = solve(source)
        assert fun(8) == 11
    with pytest.raises(UnsupportedSynthesisGoal, match="component native"):
        solve("""@example(f 1 = 3)
            def f (x:Int) : Int := let y : Int := native "x + 1" in y + ?body;""")


def test_constructor_data_limits_and_malformed_values():
    interpreter = LiftedInterpreter(forest(), {}, H)
    interpreter.constructors = {"IntList_nil": 0, "IntList_cons": 2}
    for value in (("Unknown",), ("IntList_cons", 1), (1, 2, 4), ("IntList_nil", 1)):
        with pytest.raises(UnsupportedSynthesisGoal, match="registered constructor"):
            interpreter.check_data(value)
    with pytest.raises(UnsupportedSynthesisGoal, match="Int or Bool"):
        interpreter.check_data(int_list(1.0))
    with pytest.raises(SynthesisNotSuccessful, match="data size limit"):
        interpreter.check_data(int_list(*range(34)))
