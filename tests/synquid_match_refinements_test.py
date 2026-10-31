"""MATCH preserves precise scrutinee types without inventing field invariants."""

from time import monotonic

import pytest

from aeon.compilation.session import CompilationSession
from aeon.core.substitutions import substitution
from aeon.core.terms import (
    Abstraction,
    Application,
    ImplicitRefinementHole,
    Literal,
    RefinementApplication,
    TypeApplication,
    Var,
)
from aeon.core.types import t_bool, t_int, top
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes
from aeon.synthesis.grammar.utils import SYNTHESIS_EXCLUDED_NAMES
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from tests.driver import check_and_return_core


@pytest.fixture(autouse=True)
def compilation_session():
    with CompilationSession().activate():
        yield


def hole_context(source):
    program, root, _, _ = check_and_return_core(source)
    targets = incomplete_functions_and_holes(root, program)
    hole = targets[0][1][0]
    goal, local = get_holes_info(root, program, top, targets, refined_types=True)[hole]
    return program, root, hole, goal, local


def skip(name):
    return name.name in SYNTHESIS_EXCLUDED_NAMES or name.name in {"unwrap", "choose"}


@pytest.mark.parametrize("computed", [False, True])
def test_match_preserves_abstract_element_refinement(computed):
    # An opaque q cannot be satisfied by guessing an integer literal. The
    # solution must obtain the already-refined value from the constructor.
    definitions = """
    inductive Box a forall <p:a -> Bool>
    | mk (value:a<p>) : (Box a)
    """
    if computed:
        signature = "(f:(u:Unit) -> (Box a<q>))"
    else:
        signature = "(b:(Box a<q>))"
    source = definitions + f"def unwrap : forall a:B, forall <q:a -> Bool>, {signature} -> a<q> := ?hole;"
    program, root, hole, goal, local = hole_context(source)
    mem = {"synquid_deadline": monotonic() + 15, "synquid_match_depth": 1}
    terms = synthes_memory(local, int(computed), goal, skip, mem)
    term = next(t for t in terms if check_type(local, t, goal))
    assert mem["synquid_stats"].matches >= 1
    assert "Box_rec" in str(term)
    assert check_type(root, substitution(program, term, hole), top)


def test_nested_matches_keep_refined_type_arguments():
    source = """
    inductive Box a
    | mk (value:a) : (Box a)
    def unwrap : forall a:B, forall <q:a -> Bool>, (b:(Box (Box a<q>))) -> a<q> := ?hole;
    """
    program, root, hole, goal, local = hole_context(source)
    mem = {"synquid_deadline": monotonic() + 15, "synquid_match_depth": 2}
    terms = synthes_memory(local, 0, goal, skip, mem)
    term = next(t for t in terms if check_type(local, t, goal))
    assert str(term).count("Box_rec") == 2
    assert check_type(root, substitution(program, term, hole), top)


def recursor_call(local, predicate):
    rec = next(n for n, _ in local.concrete_vars() if n.name == "Box_rec")
    scrut = next(n for n, _ in local.concrete_vars() if n.name == "b")
    field = Name("field", 99901)
    head = RefinementApplication(TypeApplication(Var(rec), t_int), predicate)
    return Application(Application(head, Var(scrut)), Abstraction(field, Var(field)))


def positive_predicate():
    arg = Name("value", 99902)
    return Abstraction(arg, Application(Application(Var(Name(">", 0)), Var(arg)), Literal(0, t_int)))


@pytest.mark.parametrize(
    "predicate",
    [
        positive_predicate(),
        Abstraction(Name("x", 99903), Literal(False, t_bool)),
        ImplicitRefinementHole(Name("implicit", 99904)),
    ],
)
def test_match_rejects_invented_predicate_on_erased_scrutinee(predicate):
    source = """
    inductive Box forall <p:Int -> Bool>
    | mk (value:Int<p>) : Box
    def unwrap (b:Box) : {v:Int | v > 0} := ?hole;
    """
    _, _, _, goal, local = hole_context(source)
    assert not check_type(local, recursor_call(local, predicate), goal)


@pytest.mark.parametrize("implicit", [False, True])
def test_match_infers_only_predicates_justified_by_scrutinee(implicit):
    source = """
    inductive Box forall <p:Int -> Bool>
    | mk (value:Int<p>) : {b:Box | view b = value}
    + view (b:Box) : Int
    def unwrap (b:{z:Box | view z > 0}) : {v:Int | v > 0} := ?hole;
    """
    _, _, _, goal, local = hole_context(source)
    predicate = ImplicitRefinementHole(Name("implicit", 99905)) if implicit else positive_predicate()
    assert check_type(local, recursor_call(local, predicate), goal)


def test_match_supports_binary_predicate_parameters():
    source = """
    inductive Duo a forall <r:a -> a -> Bool>
    | mk (first:a) (second:{v:a | r first v}) : (Duo a)
    def choose : forall a:B, forall <q:a -> Bool>, (d:(Duo a<q>)) -> a<q> := ?hole;
    """
    program, root, hole, goal, local = hole_context(source)
    mem = {"synquid_deadline": monotonic() + 15, "synquid_match_depth": 1}
    terms = synthes_memory(local, 0, goal, skip, mem)
    term = next(t for t in terms if check_type(local, t, goal))
    assert mem["synquid_stats"].matches >= 1
    assert check_type(root, substitution(program, term, hole), top)
