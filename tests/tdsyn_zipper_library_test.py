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


def test_component_library_honors_lexical_shadowing():
    """Inner ``let rest := unit`` must hide the outer projector from the grammar."""
    from aeon.core.types import t_unit
    from aeon.synthesis.modules.tdsyn.helpers import clear_tdsyn_caches
    from aeon.synthesis.modules.tdsyn.library import visible_vars

    clear_tdsyn_caches()
    rest = Name("Arch_ctor_rest", 0)
    ctor = Name("Arch_ctor", 0)
    arch_ty = t_int  # stand-in base; only names/shadowing matter here
    ctx = (
        TypingContext()
        .with_var(ctor, AbstractionType(Name("r", 0), arch_ty, arch_ty))
        .with_var(rest, AbstractionType(Name("a", 0), arch_ty, arch_ty))
        .with_var(rest, t_unit)  # hole-local shadow
    )
    visible = {n.name: t for n, t in visible_vars(ctx)}
    assert visible["Arch_ctor_rest"] == t_unit
    lib = get_component_library(ctx, lambda _: False)
    returning = [term.name.name for term, _ in lib.functions_returning(arch_ty) if isinstance(term, Var)]
    assert "Arch_ctor" in returning
    assert "Arch_ctor_rest" not in returning


def test_component_library_cache_evicted_when_context_collected():
    """A dead context's cache entry must not survive to poison a later context
    that reuses the same ``id()`` (regression: backward_close found no
    candidates when a stale library hid in-scope variables)."""
    import gc

    from aeon.synthesis.modules.tdsyn.library import _library_cache

    ctx = TypingContext().with_var(Name("n", 0), t_int)
    get_component_library(ctx, lambda _: False)
    key = id(ctx)
    assert key in _library_cache
    del ctx
    gc.collect()
    assert key not in _library_cache


def test_subtype_cache_evicted_when_context_collected():
    import gc

    from aeon.synthesis.modules.tdsyn.helpers import _subtype_cache, is_subtype

    from aeon.core.liquid import LiquidLiteralBool
    from aeon.core.types import RefinedType, t_int as int_ty

    ctx = TypingContext().with_var(Name("n", 0), t_int)
    # Populate the cache with a non-trivial pair (equal types and mismatched
    # bases short-circuit before caching).
    refined_int = RefinedType(Name("v", 0), int_ty, LiquidLiteralBool(True))
    is_subtype(ctx, refined_int, t_int)
    key = id(ctx)
    assert key in _subtype_cache
    del ctx
    gc.collect()
    assert key not in _subtype_cache


def test_monomorphize_numeric_ops_skip_adt_types():
    from aeon.core.types import AbstractionType, Kind, TypeConstructor, TypePolymorphism, TypeVar
    from aeon.synthesis.modules.tdsyn.helpers import base_type_of, get_return_type, monomorphize

    a = Name("a", 0)
    plus_ty = TypePolymorphism(
        a,
        Kind.BASE,
        AbstractionType(Name("x", 0), TypeVar(a), AbstractionType(Name("y", 0), TypeVar(a), TypeVar(a))),
    )
    ctx = TypingContext().with_var(Name("Arch_out", 0), TypeConstructor(Name("Arch", 0)))
    monos = monomorphize(Name("+", 0), plus_ty, ctx)
    bases = {base_type_of(get_return_type(ty)).name.name for _, ty in monos if isinstance(ty, AbstractionType)}
    assert bases == {"Int", "Float"}
    assert "Arch" not in bases
