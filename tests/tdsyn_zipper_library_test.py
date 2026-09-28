"""Unit tests for path-based hole substitution and the component library index."""

from aeon.core.terms import Abstraction, Application, Hole, If, Literal, Var
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.synthesis.modules.tdsyn.library import get_component_library
from aeon.synthesis.modules.tdsyn.worklist import (
    Child,
    PartialAST,
    expand_at_hole,
    fresh_hole,
    locate_holes,
    substitute_at,
    substitute_holes_map,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def test_locate_and_substitute_at_rebuilds_only_spine():
    h1 = Hole(Name("h1", 1))
    h2 = Hole(Name("h2", 2))
    tree = If(h1, Application(Var(Name("f", 0)), h2), Literal(0, t_int))
    paths = locate_holes(tree)
    assert paths[Name("h1", 1)] == (Child.COND,)
    assert paths[Name("h2", 2)] == (Child.THEN, Child.ARG)

    lit = Literal(True, t_bool)
    replaced = substitute_at(tree, paths[Name("h1", 1)], lit)
    assert isinstance(replaced, If)
    assert replaced.cond == lit
    assert replaced.then == tree.then
    assert replaced.otherwise == tree.otherwise


def test_substitute_holes_map_fills_all_in_one_walk():
    h1 = Hole(Name("a", 1))
    h2 = Hole(Name("b", 2))
    tree = Application(h1, h2)
    out = substitute_holes_map(
        tree,
        {Name("a", 1): Literal(1, t_int), Name("b", 2): Literal(2, t_int)},
    )
    assert out == Application(Literal(1, t_int), Literal(2, t_int))


def test_expand_at_hole_retargets_nested_paths():
    hole_term, typed = fresh_hole(t_int, TypingContext(), path=())
    partial = PartialAST(hole_term, [typed], 0)
    inner_term, inner = fresh_hole(t_bool, TypingContext())
    replacement = Abstraction(Name("x", 0), inner_term)
    nxt = expand_at_hole(partial, typed, replacement, [inner], depth=1)
    assert isinstance(nxt.term, Abstraction)
    assert nxt.holes[0].path == (Child.BODY,)
    assert locate_holes(nxt.term)[nxt.holes[0].name] == (Child.BODY,)


def test_component_library_indexes_by_return_and_arg_base():
    x = Name("x", 0)
    ctx = (
        TypingContext()
        .with_var(Name("n", 0), t_int)
        .with_var(
            Name("inc", 0),
            AbstractionType(x, t_int, t_int),
        )
    )
    lib = get_component_library(ctx, lambda _: False)
    returning = list(lib.functions_returning(t_int))
    assert any(isinstance(term, Var) and term.name.name == "inc" for term, _ in returning)
    accepting = list(lib.functions_accepting(t_int))
    assert any(isinstance(term, Var) and term.name.name == "inc" for term, _ in accepting)
    values = list(lib.values_matching(t_int))
    assert any(isinstance(term, Var) and term.name.name == "n" for term, _ in values)
