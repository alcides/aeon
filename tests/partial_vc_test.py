from aeon.core.terms import Literal
from aeon.core.types import TypeConstructor
from aeon.typechecking.context import TypingContext
from aeon.typechecking.partial_vc import ModularVC, build_modular_vc
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def test_build_modular_vc_entails_matches_check_type_int():
    ctx = TypingContext()
    int_t = TypeConstructor(Name("Int", 0), [])
    lit = Literal(7, int_t)
    vc = build_modular_vc(ctx, lit, int_t)
    assert isinstance(vc, ModularVC)
    assert vc.entails() == check_type(ctx, lit, int_t)


def test_modular_vc_lifted_is_constraint():
    ctx = TypingContext()
    int_t = TypeConstructor(Name("Int", 0), [])
    lit = Literal(2, int_t)
    vc = build_modular_vc(ctx, lit, int_t)
    assert vc.constraint is not None
    assert vc.lifted is not None


def test_entails_with_explicit_q_matches_entails_for_plain_int():
    ctx = TypingContext()
    int_t = TypeConstructor(Name("Int", 0), [])
    lit = Literal(0, int_t)
    vc = build_modular_vc(ctx, lit, int_t)
    q = extract_qualifier_atoms(ctx)
    assert vc.entails() == vc.entails_with_qualifiers(q)


def test_explain_failures_empty_when_entails():
    ctx = TypingContext()
    int_t = TypeConstructor(Name("Int", 0), [])
    lit = Literal(1, int_t)
    vc = build_modular_vc(ctx, lit, int_t)
    assert vc.entails()
    assert list(vc.explain_failures()) == []
