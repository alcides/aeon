"""N-ary abstract refinements: ``forall <r : a -> ... -> Bool>``.

Abstract-refinement parameters generalise from unary predicates
(``<p : a -> Bool>``) to n-ary relations (``<r : a -> a -> Bool>``, ...). The
refinement's ``sort`` now stores the *full* predicate type (a curried
``AbstractionType`` chain ending in ``Bool``); ``predicate_domains`` recovers
the domain types, and the back end (liquefaction + Horn) already handles any
arity.
"""

from __future__ import annotations

from aeon.core.substitutions import predicate_domains
from aeon.core.types import AbstractionType, TypeVar, t_bool, t_int
from aeon.sugar.parser import parse_type
from aeon.sugar.stypes import SAbstractionType, SRefinementPolymorphism
from aeon.utils.name import Name


def test_unary_refinement_sort_parses_as_predicate_type():
    ty = parse_type("forall <p : a -> Bool>, (List a)")
    assert isinstance(ty, SRefinementPolymorphism)
    # ``a -> Bool`` — a single-arrow predicate type, not nested.
    assert isinstance(ty.sort, SAbstractionType)
    assert not isinstance(ty.sort.type, SAbstractionType)


def test_binary_refinement_sort_parses_as_curried_predicate_type():
    ty = parse_type("forall <r : a -> a -> Bool>, (List a)")
    assert isinstance(ty, SRefinementPolymorphism)
    # ``a -> (a -> Bool)`` — a two-arrow (binary-relation) predicate type.
    assert isinstance(ty.sort, SAbstractionType)
    assert isinstance(ty.sort.type, SAbstractionType)


def test_ternary_refinement_sort_parses():
    ty = parse_type("forall <r : a -> a -> a -> Bool>, (List a)")
    assert isinstance(ty, SRefinementPolymorphism)
    assert isinstance(ty.sort, SAbstractionType)
    assert isinstance(ty.sort.type, SAbstractionType)
    assert isinstance(ty.sort.type.type, SAbstractionType)


def test_predicate_domains_recovers_arity():
    a = TypeVar(Name("a"))
    unary = AbstractionType(Name("_"), a, t_bool)
    assert predicate_domains(unary) == [a]

    binary = AbstractionType(Name("_"), t_int, AbstractionType(Name("_"), t_int, t_bool))
    assert predicate_domains(binary) == [t_int, t_int]
