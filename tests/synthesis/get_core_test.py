from __future__ import annotations

import pytest

from aeon.core.terms import Literal, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    Kind,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_int,
    t_float,
    t_string,
    t_bool,
)
from aeon.synthesis.grammar.grammar_generation import (
    create_literals_nodes,
    create_monomorphized_var_nodes,
    create_var_node,
    extract_all_types,
    monomorphize_poly_type,
)
from aeon.core.equality import canonicalize_type
from aeon.prelude.prelude import native_types
from aeon.utils.name import Name

types_and_values = [
    (t_bool, True),
    (t_int, 5),
    (t_float, 5.0),
    (t_string, "hello"),
]


@pytest.mark.parametrize("ty,val", types_and_values)
def test_core_literal(ty, val):
    type_info = extract_all_types([ty] + list(map(TypeConstructor, native_types)))
    literal = create_literals_nodes(type_info, [ty])[0]
    assert literal(val).get_core() == Literal(val, ty)


vars_to_test = [(Name("x", 5), t_int), (Name("t", 8), t_bool)]


@pytest.mark.parametrize("name,ty", vars_to_test)
def test_core_var(name, ty):
    type_info = extract_all_types([ty])
    node = create_var_node(name, ty, type_info[ty])

    match node().get_core():
        case Var(var_name):
            assert var_name == name
        case _:
            assert False, f"Expected Var, got {node().get_core()}"


def test_extract_all_types_poly_target():
    # forall a, List a  in TARGET position with instantiation {Int, String}
    poly = TypePolymorphism(
        Name("a", 0),
        Kind.BASE,
        TypeConstructor(Name("List", 0), [TypeVar(Name("a", 0))]),
    )
    inst = {t_int, t_string}
    data = extract_all_types([poly], instantiation_types=inst)

    assert TypeConstructor(Name("List", 0), [t_int]) in data
    assert TypeConstructor(Name("List", 0), [t_string]) in data
    # The forall node itself must NOT be registered.
    assert poly not in data


def test_extract_all_types_poly_nested_in_abstraction():
    # forall a, (x : a) -> List a : the monomorphized body is a concrete
    # AbstractionType, exercising forwarding of instantiation_types through the
    # AbstractionType recursive self-call (which registers the nested List Int).
    poly = TypePolymorphism(
        Name("a", 0),
        Kind.BASE,
        AbstractionType(
            Name("x", 0),
            TypeVar(Name("a", 0)),
            TypeConstructor(Name("List", 0), [TypeVar(Name("a", 0))]),
        ),
    )
    inst = {t_int}
    data = extract_all_types([poly], instantiation_types=inst)

    # The concrete instantiation classes are registered. `data` is keyed on the
    # alpha-equivalence canonical form (#311), so canonicalize before membership.
    assert canonicalize_type(TypeConstructor(Name("List", 0), [t_int])) in data
    assert canonicalize_type(AbstractionType(Name("x", 0), t_int, TypeConstructor(Name("List", 0), [t_int]))) in data
    assert canonicalize_type(poly) not in data


def test_extract_all_types_poly_empty_instantiation():
    # Empty instantiation set is a graceful no-op: forall not registered, no crash.
    poly = TypePolymorphism(
        Name("a", 0),
        Kind.BASE,
        TypeConstructor(Name("List", 0), [TypeVar(Name("a", 0))]),
    )
    data = extract_all_types([poly], instantiation_types=set())
    assert poly not in data
    assert TypeConstructor(Name("List", 0), [t_int]) not in data


def test_mono_var_get_core_type_application():
    # monomorphize forall a, (x:a)->a with {Int}, feed through
    # create_monomorphized_var_nodes, assert get_core() is a TypeApplication
    # with .type == t_int.
    poly = TypePolymorphism(
        Name("a", 0),
        Kind.BASE,
        AbstractionType(Name("x", 0), TypeVar(Name("a", 0)), TypeVar(Name("a", 0))),
    )
    inst = {t_int}
    mono = monomorphize_poly_type(poly, inst)
    assert mono, "expected at least one monomorphized body"

    fname = Name("f", 0)
    monomorphized = [(fname, body, type_apps) for body, type_apps in mono]

    # Register the mono body itself so the simple (no-field) var node is created.
    type_info = extract_all_types([t_int, mono[0][0]], instantiation_types=inst)
    nodes = create_monomorphized_var_nodes(monomorphized, type_info)

    # The simple var node (no constructor args) produces Var f applied to type Int.
    cores = []
    for node in nodes:
        try:
            cores.append(node().get_core())
        except TypeError:
            # var_app_ nodes require argument fields; skip those here.
            continue

    type_apps = [c for c in cores if isinstance(c, TypeApplication)]
    assert type_apps, "expected a TypeApplication-producing var node"
    ta = type_apps[0]
    assert ta.type == t_int
    assert ta.body == Var(fname)


def test_default_instantiation_universe():
    from aeon.synthesis.grammar.grammar_generation import DEFAULT_POLY_INSTANTIATION_UNIVERSE

    assert DEFAULT_POLY_INSTANTIATION_UNIVERSE == frozenset({t_int, t_float, t_bool, t_string})


def test_monomorphize_uses_full_default_universe():
    """Even with no program-derived type args, foralls instantiate over the base universe."""
    from aeon.synthesis.grammar.grammar_generation import DEFAULT_POLY_INSTANTIATION_UNIVERSE

    poly = TypePolymorphism(
        Name("a", 0),
        Kind.BASE,
        AbstractionType(Name("x", 0), TypeVar(Name("a", 0)), TypeVar(Name("a", 0))),
    )
    mono = monomorphize_poly_type(poly, set(DEFAULT_POLY_INSTANTIATION_UNIVERSE))
    apps = {tuple(type_apps) for _, type_apps in mono}
    assert apps == {(t_int,), (t_float,), (t_bool,), (t_string,)}


def test_poly_target_start_covers_all_instantiations():
    """A polymorphic hole start is a union NT with one wrapper per mono body."""
    from aeon.synthesis.grammar.grammar_generation import gen_grammar_nodes
    from aeon.typechecking.context import TypingContext

    poly = TypePolymorphism(
        Name("a", 0),
        Kind.BASE,
        AbstractionType(Name("x", 0), TypeVar(Name("a", 0)), TypeVar(Name("a", 0))),
    )
    nodes, start = gen_grammar_nodes(TypingContext(), poly, Name("synth", 0), {})
    assert start.__name__ == "poly_target_start"
    inst_names = sorted(c.__name__ for c in nodes if c.__name__.startswith("poly_inst_"))
    assert inst_names == [
        "poly_inst_æBool",
        "poly_inst_æFloat",
        "poly_inst_æInt",
        "poly_inst_æString",
    ]


def test_int_hole_monomorphizes_prelude_without_type_args():
    """Plain ``Int`` holes still get polymorphic prelude ops via the default universe."""
    from aeon.core.types import top
    from aeon.synthesis.grammar.grammar_generation import create_grammar
    from aeon.synthesis.identification import get_holes_info
    from tests.driver import check_and_return_core

    term, ctx, _ectx, _metadata = check_and_return_core("def synth (n: Int) : Int := ?hole;")
    holes = get_holes_info(ctx, term, top, [], refined_types=True)
    ty, hole_ctx = next(iter(holes.values()))
    grammar = create_grammar(hole_ctx, ty, Name("synth", 0), {})
    names = {getattr(alt, "__name__", "") for alts in grammar.alternatives.values() for alt in alts}
    # ``+`` is ``forall a. a -> a -> a``; with the default universe it must appear
    # at least at ``Int`` (and typically ``Float``).
    assert any("mono" in n and "æInt" in n for n in names), sorted(n for n in names if "mono" in n)[:20]


def test_multi_binder_monomorphize_uses_diagonal_with_program_types():
    """Multi-parameter foralls avoid the full default-universe product."""
    from aeon.synthesis.grammar.grammar_generation import DEFAULT_POLY_INSTANTIATION_UNIVERSE

    a, b = Name("a", 0), Name("b", 0)
    # forall a b. a -> b -> a
    poly = TypePolymorphism(
        a,
        Kind.BASE,
        TypePolymorphism(
            b,
            Kind.BASE,
            AbstractionType(
                Name("x", 0),
                TypeVar(a),
                AbstractionType(Name("y", 0), TypeVar(b), TypeVar(a)),
            ),
        ),
    )
    inst = set(DEFAULT_POLY_INSTANTIATION_UNIVERSE)
    program = {t_float}
    mono = monomorphize_poly_type(poly, inst, program)
    apps = {tuple(type_apps) for _, type_apps in mono}
    # Full product over program types + diagonal over the default universe.
    assert (t_float, t_float) in apps
    assert (t_int, t_int) in apps
    assert (t_bool, t_bool) in apps
    assert (t_string, t_string) in apps
    # Cross terms from the default universe alone must not appear.
    assert (t_int, t_float) not in apps
    assert (t_float, t_int) not in apps
    assert len(apps) == 4
