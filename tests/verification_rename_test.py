"""Renaming preserves dependent contracts while skipping unrelated syntax."""

import pytest
from hypothesis import given, settings, strategies as st

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidLiteralInt, LiquidPredicate, LiquidVar
from aeon.core.types import AbstractionType, LiquidHornApplication, RefinedType, Type, TypeConstructor, t_int
from aeon.utils.name import Name
from aeon.verification.smt import _RenameOccurrences, flatten, rename_constraint, smt_valid
from aeon.verification.vcs import (
    Conjunction,
    Implication,
    LiquidConstraint,
    ReflectedFunctionDeclaration,
    UninterpretedFunctionDeclaration,
)


def equals(left, right):
    return LiquidApp(Name("==", 0), [left, right])


@given(value=st.integers(-100, 100), delta=st.integers(-2, 2), reflected=st.booleans())
@settings(max_examples=40, deadline=None)
def test_renaming_preserves_dependent_function_proofs(value, delta, reflected):
    old, new, formal, result, function = (Name(n, 19100) for n in ("outer", "renamed", "arg", "ret", "helper"))
    signature = AbstractionType(formal, t_int, RefinedType(result, t_int, equals(LiquidVar(result), LiquidVar(old))))
    call = LiquidApp(function, [LiquidLiteralInt(0)])
    conclusion = LiquidConstraint(equals(call, LiquidLiteralInt(value + delta)))
    declaration = (
        ReflectedFunctionDeclaration(function, signature, (formal,), LiquidVar(old), conclusion)
        if reflected
        else UninterpretedFunctionDeclaration(function, signature, conclusion)
    )
    original = Implication(old, t_int, equals(LiquidVar(old), LiquidLiteralInt(value)), declaration)
    renamed = Implication(
        new, t_int, equals(LiquidVar(new), LiquidLiteralInt(value)), rename_constraint(declaration, old, new)
    )
    assert smt_valid(original) == (delta == 0)
    assert smt_valid(renamed) == (delta == 0)


def test_unrelated_function_types_keep_their_identity(monkeypatch):
    old, new, formal, function = (Name(n, 19200) for n in ("old", "new", "arg", "helper"))
    signature = AbstractionType(formal, t_int, t_int)
    body = LiquidConstraint(equals(LiquidVar(old), LiquidLiteralInt(3)))
    declaration = UninterpretedFunctionDeclaration(function, signature, body, is_refinement=True)

    def unexpected_rewrite(*args):
        raise AssertionError("An unrelated library signature was traversed for substitution")

    monkeypatch.setattr("aeon.verification.smt.substitution_in_type", unexpected_rewrite)
    renamed = rename_constraint(declaration, old, new)
    assert renamed.type is signature
    assert renamed.is_refinement
    assert renamed.seq.expr == equals(LiquidVar(new), LiquidLiteralInt(3))


@pytest.mark.parametrize("implicit", [False, True])
def test_predicate_arguments_and_horn_arguments_are_not_skipped(implicit):
    old, new, element, formal = (Name(n, 19300) for n in ("old", "new", "element", "formal"))
    predicate = LiquidPredicate((element,), equals(LiquidVar(element), LiquidVar(old)), implicit=implicit)
    carrier = TypeConstructor(Name("Container", 19300), [t_int], refinements=[predicate])
    signature = AbstractionType(formal, carrier, t_int)
    horn = LiquidHornApplication(Name("k", 19300), [(LiquidVar(old), t_int)])
    declaration = UninterpretedFunctionDeclaration(Name("helper", 19300), signature, LiquidConstraint(horn))
    renamed = rename_constraint(declaration, old, new)
    assert renamed.type.var_type.refinements[0].body == equals(LiquidVar(element), LiquidVar(new))
    assert renamed.seq.expr.argtypes[0][0] == LiquidVar(new)


def test_a_later_rename_observes_mutated_type_syntax():
    old, new, formal, result = (Name(n, 19400) for n in ("old", "new", "formal", "result"))
    ret = RefinedType(result, t_int, LiquidLiteralBool(True))
    signature = AbstractionType(formal, t_int, ret)
    declaration = UninterpretedFunctionDeclaration(Name("helper", 19400), signature, LiquidConstraint(LiquidVar(old)))
    assert rename_constraint(declaration, old, new).type is signature
    ret.refinement = equals(LiquidVar(result), LiquidVar(old))
    renamed = rename_constraint(declaration, old, new)
    assert renamed.type.type.refinement == equals(LiquidVar(result), LiquidVar(new))


def test_unknown_type_payloads_disable_the_occurrence_shortcut():
    class OpaqueType(Type):
        pass

    assert _RenameOccurrences().contains(OpaqueType(), Name("possibly_present", 19500))


def test_shared_sibling_predicates_keep_independent_smt_bindings():
    name = Name("sibling", 19600)
    shared = LiquidConstraint(equals(LiquidVar(name), LiquidLiteralInt(1)))
    constraints = Conjunction(
        Implication(name, t_int, equals(LiquidVar(name), LiquidLiteralInt(1)), shared),
        Implication(name, t_int, equals(LiquidVar(name), LiquidLiteralInt(2)), shared),
    )
    clauses = list(flatten(constraints))
    assert len(clauses) == 2
    assert set(clauses[0].variables).isdisjoint(clauses[1].variables)
    assert not smt_valid(constraints)
