"""Size-recurrence pruning and diamond alignment, through the real compiler."""

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Application, Var
from aeon.core.types import top
from aeon.synthesis.api import SynthesisNotSuccessful, UnsupportedSynthesisGoal
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.fitness_eval import set_program_tail
from aeon.synthesis.identification import incomplete_functions_and_holes, iterate_top_level
from aeon.synthesis.modules.structure_guided import StructureGuidedSynthesizer
from aeon.synthesis.modules.structure_guided.search import Config, Example, Node, Recurrence, Search
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type
from tests.joint_hole_synthesis_test import parse


def chain(*values):
    node = None
    for value in reversed(values):
        node = Node((value,), (node,))
    return node


def test_size_inference_retains_ambiguous_models():
    search = Search((Example(chain(7), (7,)),), 1, Config(), 2)
    relations = search.recurrences()
    assert all(Recurrence((a,), 1, 0) in relations for a in (0, 1, 2))


def test_stutter_prunes_one_constructor_before_element_search():
    search = Search((Example(None, ()), Example(chain(2), (2, 2)), Example(chain(1, 3), (1, 1, 3, 3))), 1, Config(), 2)
    relations = search.recurrences()
    assert relations == (Recurrence((1,), 2, 0),)
    words = list(search.words(relations))
    assert ((-1, 0), 0) not in words and ((-1, -1, 0), 0) in words
    assert search.stats.pruned > 0 and search.stats.local_tasks == 0


def test_alignment_derives_different_element_tasks_at_two_positions():
    search = Search((Example(chain(2, 4), (2, 3, 4, 5)),), 1, Config(), 2)
    tasks = search.align((-1, -1, 0), 0)
    assert tasks == {(1, 0): {(2,): 2, (4,): 4}, (1, 1): {(2,): 3, (4,): 5}}
    expr = search.element(tasks[(1, 1)])
    assert expr is not None and expr.evaluate((99,)) == 100


def test_alignment_rejects_inconsistent_repeated_diamonds():
    search = Search((Example(chain(2, 2), (2, 3)),), 1, Config(), 2)
    assert search.align((-1, 0), 0) is None and search.stats.local_tasks == 0


def test_tree_recurrence_and_preorder_alignment():
    tree = Node((3,), (Node((1,), (None, None)), Node((7,), (None, None))))
    search = Search((Example(None, ()), Example(tree, (3, 1, 7))), 2, Config(), 2)
    assert Recurrence((1, 1), 1, 0) in search.recurrences()
    assert search.align((-1, 0, 1), 0) == {(1, 0): {(3,): 3, (1,): 1, (7,): 7}}


def test_local_element_enumeration_composes_arithmetic():
    search = Search((Example(None, ()),), 1, Config(), 2)
    expression = search.element({(1,): 3, (2,): 7, (3,): 13, (4,): 21})
    assert expression is not None and expression.evaluate((10,)) == 111


def test_nonempty_base_and_multiple_recursive_calls_are_inferred():
    search = Search((Example(None, (0,)), Example(chain(2), (2, 0)), Example(chain(1, 3), (1, 3, 0))), 1, Config(), 2)
    assert search.recurrences() == (Recurrence((1,), 1, 1),)
    tasks = search.align((-1, 0), 1)
    assert tasks[(0, 0)] == {(): 0}
    doubled = Search((Example(None, ()), Example(chain(1), (1,)), Example(chain(1, 2), (1, 2, 2))), 1, Config(), 2)
    assert doubled.recurrences() == (Recurrence((2,), 1, 0),)
    assert doubled.align((-1, 0, 0), 0) == {(1, 0): {(1,): 1, (2,): 2}}


LIST = """
inductive Chain
| nil : Chain
| cons (head:Int) (tail:Chain) : Chain
"""


def literal(values, tag="Chain"):
    result = f"{tag}.nil"
    for value in reversed(values):
        scalar = str(value) if value >= 0 else f"(0 - {-value})"
        result = f"{tag}.cons {scalar} ({result})"
    return result


def solve_source(source, backend=None):
    driver = parse(source)
    backend = backend or StructureGuidedSynthesizer()
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    with driver.session.activate():
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            targets,
            driver.metadata,
            backend,
            budget=10,
            ui=SilentSynthesisUI(),
        )
    completed = driver.core
    for name, candidate in mapping.items():
        assert candidate is not None
        completed = substitution(completed, candidate, name)
    with driver.session.activate():
        assert check_type(driver.typing_ctx, completed, top)
    return driver, completed, backend


def run_on(driver, completed, input_value):
    from aeon.utils.name import Name

    name = next(d.var_name for d in iterate_top_level(completed) if d.var_name.name == "f")
    value_name = Name("held_out", 999999)
    term = Application(Var(name), Var(value_name))
    with driver.session.activate():
        return aeon_eval(set_program_tail(completed, term), driver.evaluation_ctx.with_var(value_name, input_value))


def runtime_list(values):
    result = ("Chain_nil",)
    for value in reversed(values):
        result = ("Chain_cons", value, result)
    return result


@pytest.mark.parametrize("kind", ["stutter", "reverse", "map", "paired_map"])
def test_real_recursive_programs_execute_on_held_out_inputs(kind):
    transforms = {
        "stutter": lambda xs: [v for x in xs for v in (x, x)],
        "reverse": lambda xs: xs[::-1],
        "map": lambda xs: [x + 1 for x in xs],
        "paired_map": lambda xs: [v for x in xs for v in (x, x + 1)],
    }
    transform = transforms[kind]
    rows = [[], [2], [1, 3], [4, 2, 1]]
    examples = "\n".join(f"@example(f ({literal(xs)}) = ({literal(transform(xs))}))" for xs in rows)
    driver, completed, backend = solve_source(LIST + examples + "\n@allow_recursion\ndef f(xs:Chain):Chain := ?hole;")
    assert run_on(driver, completed, runtime_list([9, 5, -2])) == runtime_list(transform([9, 5, -2]))
    assert backend.stats.recurrences >= 1 and backend.stats.aligned >= 1 and backend.stats.candidates >= 1


def test_recursive_tree_traversal_executes_with_local_append():
    source = (
        LIST
        + """
    inductive Tree
    | leaf : Tree
    | branch (left:Tree) (value:Int) (right:Tree) : Tree
    @example(f Tree.leaf = Chain.nil)
    @example(f (Tree.branch Tree.leaf 1 Tree.leaf) = Chain.cons 1 Chain.nil)
    @example(f (Tree.branch (Tree.branch Tree.leaf 2 Tree.leaf) 1 (Tree.branch Tree.leaf 3 Tree.leaf)) = Chain.cons 2 (Chain.cons 1 (Chain.cons 3 Chain.nil)))
    @allow_recursion
    def f(t:Tree):Chain := ?hole;
    """
    )
    driver, completed, backend = solve_source(source)
    leaf = ("Tree_leaf",)
    tree = ("Tree_branch", leaf, 9, ("Tree_branch", leaf, 5, leaf))
    assert run_on(driver, completed, tree) == runtime_list([9, 5])
    assert backend.stats.pruned > 0


def test_inconsistent_structural_examples_fail_cleanly():
    search = Search((Example(chain(1), (1,)), Example(chain(2), (2, 2))), 1, Config(), 2)
    with pytest.raises(SynthesisNotSuccessful, match="no size recurrence"):
        next(search.solutions())


def test_search_limits_and_timeout():
    with pytest.raises(SynthesisNotSuccessful, match="time budget"):
        Search((Example(None, ()),), 1, Config(), 0)
    search = Search((Example(chain(1), (1, 1)),), 1, Config(max_skeletons=1), 2)
    with pytest.raises(SynthesisNotSuccessful, match="skeleton limit"):
        list(search.words(search.recurrences()))
    with pytest.raises(UnsupportedSynthesisGoal, match="structural bounds"):
        Search((Example(chain(1, 2, 3), ()),), 1, Config(max_depth=1), 2)


def test_registration():
    from aeon.lsp.server import SYNTHESIZERS
    from aeon.synthesis.modules.synthesizerfactory import make_synthesizer, synthesizer_family, SynthesizerFamily

    assert isinstance(make_synthesizer("structure_guided"), StructureGuidedSynthesizer)
    assert "structure_guided" in SYNTHESIZERS
    assert synthesizer_family("structure_guided") == SynthesizerFamily.EXAMPLE_DRIVEN


def test_parametric_list_with_reordered_constructor_fields():
    source = """
    inductive Chain a
    | cons (tail:(Chain a)) (head:a) : (Chain a)
    | nil : (Chain a)
    @example(f (Chain.nil{Int}) = (Chain.nil{Int}))
    @example(f (Chain.cons{Int} (Chain.nil{Int}) 2) = Chain.cons{Int} (Chain.nil{Int}) 3)
    @example(f (Chain.cons{Int} (Chain.cons{Int} (Chain.nil{Int}) 5) 3) = Chain.cons{Int} (Chain.cons{Int} (Chain.nil{Int}) 6) 4)
    @allow_recursion
    def f(xs:(Chain Int)):(Chain Int) := ?hole;
    """
    driver, completed, _ = solve_source(source)
    assert run_on(driver, completed, ("Chain_cons", ("Chain_nil",), 20)) == ("Chain_cons", ("Chain_nil",), 21)


def test_standard_list_library_with_abstract_refinements():
    source = """
    import List;
    @example(f (List.nil{Int}) = (List.nil{Int}))
    @example(f (List.cons{Int} 2 (List.nil{Int})) = List.cons{Int} 3 (List.nil{Int}))
    @example(f (List.cons{Int} 1 (List.cons{Int} 4 (List.nil{Int}))) = List.cons{Int} 2 (List.cons{Int} 5 (List.nil{Int})))
    @allow_recursion
    def f(xs:(List Int)):(List Int) := ?hole;
    """
    driver, completed, _ = solve_source(source)
    assert run_on(driver, completed, ("List_cons", 9, ("List_nil",))) == ("List_cons", 10, ("List_nil",))


@pytest.mark.parametrize("valid_but_wrong", [False, True])
def test_candidate_must_pass_validation_and_actual_example_execution(monkeypatch, valid_but_wrong):
    from aeon.core.terms import Literal
    from aeon.core.types import t_bool
    from aeon.synthesis.modules.structure_guided import synthesizer as module

    original = module.core_candidate

    def replace(ctx, input_shape, output_shape, *args):
        if valid_but_wrong:
            return output_shape.empty_head  # valid type, wrong nonempty outputs
        return Literal(True, t_bool)

    monkeypatch.setattr(module, "core_candidate", replace)
    backend = StructureGuidedSynthesizer()
    with pytest.raises(SynthesisNotSuccessful, match="no validated program"):
        solve_source(
            LIST
            + """
            @example(f Chain.nil = Chain.nil)
            @example(f (Chain.cons 2 Chain.nil) = Chain.cons 2 Chain.nil)
            @example(f (Chain.cons 1 (Chain.cons 3 Chain.nil)) = Chain.cons 1 (Chain.cons 3 Chain.nil))
            @allow_recursion
            def f(xs:Chain):Chain := ?hole;
        """,
            backend,
        )
    if valid_but_wrong:
        assert backend.stats.runtime_rejections > 0
    else:
        assert backend.stats.validation_rejections > 0 and backend.stats.runtime_rejections == 0
    monkeypatch.setattr(module, "core_candidate", original)


def test_configuration_and_local_value_limits(monkeypatch):
    monkeypatch.setenv("AEON_STRUCTURE_MAX_ADDED", "5")
    assert StructureGuidedSynthesizer().config.max_added == 5
    monkeypatch.setenv("AEON_STRUCTURE_MAX_ADDED", "nonsense")
    with pytest.raises(UnsupportedSynthesisGoal, match="integers"):
        StructureGuidedSynthesizer()
    with pytest.raises(UnsupportedSynthesisGoal, match="nonnegative"):
        Config(max_added=-1)
    search = Search((Example(None, ()),), 1, Config(max_values=1), 2)
    with pytest.raises(SynthesisNotSuccessful, match="value limit"):
        search.element({(2,): 3, (4,): 5})


@pytest.mark.parametrize(
    "source, message",
    [
        ("def f(xs:Chain):Chain := ?hole;", "constructor-literal"),
        ("@example(f Chain.nil = Chain.nil) def f(xs:Chain):Chain := ?hole;", "allow_recursion"),
        ("@example(f Chain.nil = 0) @allow_recursion def f(xs:Chain):Int := ?hole;", "recursive ADTs"),
    ],
)
def test_unsupported_goals_fail_explicitly(source, message):
    with pytest.raises(UnsupportedSynthesisGoal, match=message):
        solve_source(LIST + source)
