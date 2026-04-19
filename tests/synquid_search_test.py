from unittest.mock import patch

from aeon.core.terms import Application, Literal, Var
from aeon.core.types import TypeConstructor
from aeon.synthesis.modules.synquid import build as synquid_build
from aeon.synthesis.modules.synquid.modular import application_subgoal_types, check_hole_term
from aeon.synthesis.modules.synquid.search import (
    iter_candidates_size_then_level,
    sorted_level_candidates,
    term_size,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

_INT = TypeConstructor(Name("Int", 0), [])


def test_build_reexports_search_helpers():
    assert synquid_build.term_size is term_size
    assert synquid_build.sorted_level_candidates is sorted_level_candidates
    assert synquid_build.iter_candidates_size_then_level is iter_candidates_size_then_level
    assert synquid_build.application_subgoal_types is application_subgoal_types
    assert synquid_build.check_hole_term is check_hole_term


def test_term_size_counts_nodes():
    x = Var(Name("x", 0))
    lit = Literal(1, _INT)
    app = Application(Application(Var(Name("<=", 0)), x), lit)
    assert term_size(x) == 1
    assert term_size(lit) == 1
    assert term_size(app) >= 3


def test_sorted_level_candidates_orders_by_term_size():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    large = Application(
        Application(Var(Name("+", 0)), Literal(1, _INT)),
        Literal(2, _INT),
    )
    small = Literal(0, _INT)
    assert term_size(large) > term_size(small)
    mem: dict = {(ctx, 0, _INT): [large, small]}
    ordered = list(sorted_level_candidates(ctx, 0, _INT, skip, mem))
    assert ordered == [small, large]


def test_iter_candidates_size_then_level_prefers_smaller_ast_across_levels():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    mem: dict = {}
    tiny = Literal(7, _INT)
    huge = Application(
        Application(
            Application(Var(Name("+", 0)), Literal(1, _INT)),
            Literal(2, _INT),
        ),
        Literal(3, _INT),
    )
    assert term_size(huge) > term_size(tiny)

    def fake_sorted(ctx, level, ret_t, skip_arg, mem_arg):
        if level == 0:
            yield huge
        elif level == 1:
            yield tiny

    with patch("aeon.synthesis.modules.synquid.search.sorted_level_candidates", side_effect=fake_sorted):
        out = list(iter_candidates_size_then_level(ctx, _INT, skip, mem, max_level=4, seed_levels=2))
    assert out[0] is tiny
    assert huge in out


def test_iter_candidates_max_level_zero_is_level_zero_only():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    mem: dict = {}
    merged = list(
        iter_candidates_size_then_level(ctx, _INT, skip, mem, max_level=0, seed_levels=1),
    )
    mem2: dict = {}
    expected = list(sorted_level_candidates(ctx, 0, _INT, skip, mem2))
    assert merged == expected
