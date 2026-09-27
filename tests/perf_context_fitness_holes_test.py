"""Unit tests for context extension, fitness suffix reuse, and hole pruning."""

from aeon.core.terms import Abstraction, Application, Hole, Let, Literal, Rec, Var
from aeon.core.types import t_bool, t_int
from aeon.synthesis.fitness_eval import extract_suffix, memoize_fitness
from aeon.synthesis.identification import term_has_holes
from aeon.typechecking.context import TypeConstructorBinder, TypingContext, VariableBinder
from aeon.utils.name import Name


def test_with_var_preserves_builtins_without_rescan():
    ctx = TypingContext()
    builtin_names = {e.name.name for e in ctx.entries if isinstance(e, TypeConstructorBinder)}
    assert "Int" in builtin_names
    n = len(ctx.entries)
    extended = ctx.with_var(Name("x", 0), t_int)
    assert len(extended.entries) == n + 1
    assert isinstance(extended.entries[-1], VariableBinder)
    assert extended.entries[-1].name.name == "x"
    # Builtins still present; extension skipped re-injection.
    assert not extended._ensure_builtins
    assert {e.name.name for e in extended.entries if isinstance(e, TypeConstructorBinder)} == builtin_names


def test_extract_suffix_skips_prefix_without_eval():
    f = Name("f", 0)
    g = Name("g", 0)
    hole = Hole(Name("h", 0))
    prog = Rec(g, t_int, Literal(1, t_int), Rec(f, t_int, hole, Literal(0, t_int)))
    suffix = extract_suffix(prog, f)
    assert isinstance(suffix, Rec)
    assert suffix.var_name == f
    assert suffix.var_value == hole


def test_memoize_fitness_lru_evicts_oldest():
    calls: list[int] = []

    def compute(term):
        calls.append(term.value)
        return term.value

    memo = memoize_fitness(compute, maxsize=2)
    a, b, c = Literal(1, t_int), Literal(2, t_int), Literal(3, t_int)
    assert memo(a) == 1
    assert memo(b) == 2
    assert memo(a) == 1  # hit
    assert memo(c) == 3  # evicts b
    assert memo(b) == 2  # miss after eviction
    assert calls == [1, 2, 3, 2]


def test_term_has_holes_ignores_refinement_free_trees():
    assert term_has_holes(Hole(Name("h", 0)))
    assert not term_has_holes(Literal(1, t_int))
    assert term_has_holes(Application(Var(Name("f", 0)), Hole(Name("h", 0))))
    assert not term_has_holes(Let(Name("x", 0), Literal(True, t_bool), Literal(0, t_int)))
    assert term_has_holes(Abstraction(Name("x", 0), Hole(Name("h", 0))))
