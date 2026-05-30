from __future__ import annotations

import pytest

from aeon.core.terms import Literal, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    BaseKind,
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
        BaseKind(),
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
        BaseKind(),
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
        BaseKind(),
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
        BaseKind(),
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
