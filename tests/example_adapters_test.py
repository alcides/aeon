"""Shared specification datasets retain types, labels and validation semantics."""

import pytest

from aeon.backend.evaluator import eval as evaluate
from aeon.core.terms import Let, Literal, Rec, Var
from aeon.core.types import t_int
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.example_adapters import adapt_example_metadata, derive_property_examples
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.pbt.runner import PropertyCorpus, PropertySpec
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from tests.driver import check_and_return_core
from tests.synthesis_specifications_test import solve


@pytest.mark.parametrize("file", [False, True])
@pytest.mark.parametrize(
    "data,signature,body,rows,loss",
    [
        ("1,2\n4,5", "(x:Int) : Int", "x+1", [([1], 2), ([4], 5)], 0),
        ("true,false\nfalse,true", "(x:Bool) : Bool", "!x", [([True], False), ([False], True)], 0),
        ("hello,hello\nworld,world", "(x:String) : String", "x", [(["hello"], "hello"), (["world"], "world")], 0),
        (",\n hello, hello", "(x:String) : String", "x", [([""], ""), ([" hello"], " hello")], 0),
        ("1,1.5\n2,2.5", "(x:Int) : Float", "1.5", [([1], 1.5), ([2], 2.5)], 1.0),
        ("1,3\n2,4", "(x:{v:Int | v > 0}) : Int", "x+2", [([1], 3), ([2], 4)], 0),
    ],
)
def test_typed_csv_helpers_and_metadata(file, data, signature, body, rows, loss, tmp_path):
    path = tmp_path / "typed.csv"
    path.write_text(data)
    escaped = data.replace("\n", "\\n")
    decorator = f'@csv_file("{path}")' if file else f'@csv_data("{escaped}")'
    core, _, ectx, metadata = check_and_return_core(f"{decorator} def f {signature} := {body};")
    entry = next(value for name, value in metadata.items() if name.name == "f")
    assert entry["csv_examples"] == rows
    assert [[type(value) for value in [*inputs, output]] for inputs, output in entry["csv_examples"]] == [
        [type(value) for value in [*inputs, output]] for inputs, output in rows
    ]
    assert evaluate(set_program_tail(core, Var(entry["goals"][0].function)), ectx) == loss
    assert bool(entry.get("training_data")) == all(
        type(value) in (int, float) for row in rows for value in [*row[0], row[1]]
    )


@pytest.mark.parametrize(
    "data,signature,message",
    [
        ("1,2,3", "(x:Int) : Int", "columns"),
        ("1.5,2", "(x:Int) : Int", "invalid"),
        ("yes,true", "(x:Bool) : Bool", "invalid"),
        ("nan,1.0", "(x:Float) : Float", "invalid"),
        ("", "(x:Int) : Int", "at least one row"),
    ],
)
def test_typed_csv_rejects_malformed_data(data, signature, message):
    with pytest.raises((ValueError, AssertionError), match=message):
        check_and_return_core(f'@csv_data("{data}") def f {signature} := ?h;')


def property_fixture(body, *, prefix="", target="def f (x:Int) : Int := ?h;"):
    core, ctx, ectx, metadata = check_and_return_core(f"{prefix} {target} @property(3) def p (x:Int) : Bool := {body};")
    current = core
    names = {}
    while isinstance(current, (Let, Rec)):
        names[current.var_name.name] = current.var_name
        current = current.body
    corpus = PropertyCorpus(PropertySpec(names["p"], (), 3), tuple((Literal(x, t_int),) for x in (-1, 0, 1)))
    return core, ctx, ectx, metadata, names["f"], [corpus]


@pytest.mark.parametrize("assertion", ["f (x+1) = (x+2)", "(x+2) = f (x+1)"])
def test_property_equations_generate_exact_typed_datasets(assertion):
    core, _, ectx, _, function, corpora = property_fixture(assertion)
    entry = derive_property_examples(core, ectx, function, corpora)
    assert entry["io_examples"] == [([0], 1), ([1], 2), ([2], 3)]
    assert entry["training_data"] == [[0, 1], [1, 2], [2, 3]]
    assert entry["property_examples"] == entry["constructor_io_examples"]


def test_property_expected_side_can_call_independent_helpers():
    core, _, ectx, _, function, corpora = property_fixture(
        "f x = reference x", prefix="def reference (n:Int) : Int := n+1;"
    )
    entry = derive_property_examples(core, ectx, function, corpora)
    assert entry["io_examples"] == [([-1], 0), ([0], 1), ([1], 2)]


@pytest.mark.parametrize(
    "assertion", ["f x >= x", "f x = f (0-x)", "if x > 0 then f x = 1 else true", "f x = x || f x = 0"]
)
def test_relational_or_conditional_properties_do_not_fabricate_labels(assertion):
    core, _, ectx, _, function, corpora = property_fixture(assertion)
    assert derive_property_examples(core, ectx, function, corpora) == {}


def test_property_contradictions_are_preserved_and_original_metadata_untouched():
    core, ctx, ectx, metadata, function, corpora = property_fixture("f x = 1 && f x = 2")
    original = {"io_examples": [([0], 3)], "csv_examples": [([0], 4)]}
    adapted = adapt_example_metadata(ctx, ectx, core, function, original, corpora)
    assert [([0], value) for value in (1, 2, 3, 4)] == sorted(
        [row for row in adapted["io_examples"] if row[0] == [0]], key=lambda row: row[1]
    )
    assert original == {"io_examples": [([0], 3)], "csv_examples": [([0], 4)]}


def test_property_indirect_dependency_on_target_cannot_be_a_label():
    core, _, ectx, _, function, corpora = property_fixture(
        "f x = helper x", target="def f (x:Int) : Int := ?h; def helper (x:Int) : Int := f x;"
    )
    assert derive_property_examples(core, ectx, function, corpora) == {}


@pytest.mark.parametrize("backend", ["decision_tree", "afta", "bustle_baseline", "contata", "arborist"])
def test_learners_synthesize_from_properties_without_manual_examples(backend):
    result = solve(
        "def f (x:Int) : Int := ?h; @property(4) def p (x:Int) : Bool := f x = 1;", make_synthesizer(backend), budget=3
    )
    assert result and all(term is not None for term in result.values())


@pytest.mark.parametrize("backend", ["decision_tree", "afta", "bustle_baseline", "contata", "arborist"])
def test_learners_accept_integer_csv_and_property_combination(backend):
    source = r'@csv_data("0,1\n2,1") def f (x:Int) : Int := ?h; @property(4) def p (x:Int) : Bool := f x = 1;'
    result = solve(source, make_synthesizer(backend), budget=3)
    assert result and all(term is not None for term in result.values())


@pytest.mark.parametrize("backend", ["decision_tree", "afta", "bustle_baseline", "contata", "arborist"])
def test_learners_use_evaluated_examples_and_retain_general_assertions(backend):
    source = "@example(f (1+1) = 1) @example(f 0 > 0) def f (x:Int) : Int := ?h;"
    result = solve(source, make_synthesizer(backend), budget=3)
    assert result and all(term is not None for term in result.values())


@pytest.mark.parametrize("backend", ["afta", "bustle_baseline", "arborist"])
def test_derived_examples_do_not_replace_original_property_validation(backend):
    source = "@example(f (1+1) = 1) def f (x:Int) : Int := ?h; @property(3) def p (x:Int) : Bool := f x > f x;"
    try:
        result = solve(source, make_synthesizer(backend), budget=0.5)
    except SynthesisNotSuccessful:
        return
    assert result and all(term is None for term in result.values())


@pytest.mark.parametrize("backend", ["decision_tree", "afta", "bustle_baseline", "contata", "arborist"])
def test_learners_combine_csv_properties_refinements_and_size(backend):
    source = r"""
        @csv_data("0,1\n2,1")
        @minimize_size
        def f (x:Int) : {v:Int | v >= 0} := ?h;
        @property(3) def p (x:Int) : Bool := f x = 1;
    """
    implementation = make_synthesizer(backend)
    result = solve(source, implementation, budget=1)
    assert result and all(term is not None for term in result.values())
