from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Annotation, Application, Literal, Var
from aeon.core.types import TypeConstructor
from aeon.synthesis.modules.synquid.guards import (
    bool_pairwise_conjunctions,
    bool_quad_conjunctions,
    bool_terms_from_qualifier_atoms,
    bool_triple_conjunctions,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def _is_and_annotation(t) -> bool:
    match t:
        case Annotation(Application(Application(Var(op), _), _), _):
            return op.name == "&&"
        case _:
            return False


def test_bool_pairwise_conjunctions_requires_two_singles():
    # With no in-scope Int variable, the harvested atom's operand is out of scope
    # and template instantiation (which needs an Int operand in scope) cannot
    # fire, so fewer than two singles exist and no pairwise guard is formed.
    x = Name("x", 0)
    empty_ctx = TypingContext()
    one = frozenset({LiquidApp(Name("<=", 0), [LiquidVar(x), LiquidLiteralInt(1)])})
    assert bool_terms_from_qualifier_atoms(empty_ctx, one) == []
    assert bool_pairwise_conjunctions(empty_ctx, one) == []
    x_int = TypingContext().with_var(x, TypeConstructor(Name("Int", 0), []))
    two = frozenset(
        {
            LiquidApp(Name("<=", 0), [LiquidVar(x), LiquidLiteralInt(10)]),
            LiquidApp(Name(">=", 0), [LiquidVar(x), LiquidLiteralInt(0)]),
        }
    )
    singles = bool_terms_from_qualifier_atoms(x_int, two)
    assert len(singles) >= 2
    pairs = bool_pairwise_conjunctions(x_int, two, max_singles=12, max_pairs=24)
    assert len(pairs) >= 1
    assert all(_is_and_annotation(p) for p in pairs)


def test_template_instantiation_over_in_scope_int_vars():
    # Liquid-abduction qualifier templates (Synquid PLDI'16 §2): a single
    # relational atom ``a <= 1`` is a ``⋆ <= ⋆`` template, re-instantiated over
    # the in-scope Int variables (here ``a`` and ``b``) -- surfacing the
    # cross-variable guard ``a <= b`` that the harvested atom never mentions.
    a, b = Name("a", 0), Name("b", 0)
    int_t = TypeConstructor(Name("Int", 0), [])
    ctx = TypingContext().with_var(a, int_t).with_var(b, int_t)
    atoms = frozenset({LiquidApp(Name("<=", 0), [LiquidVar(a), LiquidLiteralInt(1)])})
    singles = bool_terms_from_qualifier_atoms(ctx, atoms)

    def _rel(t, op, lhs, rhs):
        match t:
            case Annotation(Application(Application(Var(o), x), y), _):
                return o.name == op and _leaf(x) == lhs and _leaf(y) == rhs
            case _:
                return False

    def _leaf(t):
        match t:
            case Var(n):
                return n.name
            case Literal(v, _):
                return v
            case _:
                return None

    assert any(_rel(s, "<=", "a", "b") for s in singles), [str(s) for s in singles]
    # constant-only guards (e.g. ``0 <= 1``) are excluded
    assert not any(_rel(s, "<=", 0, 1) for s in singles)


def _is_triple_and_annotation(t) -> bool:
    """``((a && b) && c)`` as ``Application(Application(&&, App(App(&&,a),b)), c)``."""
    match t:
        case Annotation(Application(Application(Var(op), inner), _), _):
            if op.name != "&&":
                return False
            match inner:
                case Application(Application(Var(op2), _), _):
                    return op2.name == "&&"
                case _:
                    return False
        case _:
            return False


def test_bool_triple_conjunctions_need_three_singles():
    x = Name("x", 0)
    int_t = TypeConstructor(Name("Int", 0), [])
    ctx = TypingContext().with_var(x, int_t)
    three = frozenset(
        {
            LiquidApp(Name("<=", 0), [LiquidVar(x), LiquidLiteralInt(10)]),
            LiquidApp(Name(">=", 0), [LiquidVar(x), LiquidLiteralInt(0)]),
            LiquidApp(Name("!=", 0), [LiquidVar(x), LiquidLiteralInt(5)]),
        }
    )
    triples = bool_triple_conjunctions(ctx, three, max_singles=12, max_triples=24)
    assert len(triples) >= 1
    assert all(_is_triple_and_annotation(t) for t in triples)


def _and_chain_depth(t) -> int:
    """Left-associated ``&&`` depth (``a`` branch), matching ``guards`` output."""
    match t:
        case Annotation(inner, _):
            return _and_chain_depth(inner)
        case Application(Application(Var(op), left), _) if op.name == "&&":
            return 1 + _and_chain_depth(left)
        case _:
            return 0


def test_bool_quad_conjunctions_need_four_singles():
    x = Name("x", 0)
    int_t = TypeConstructor(Name("Int", 0), [])
    ctx = TypingContext().with_var(x, int_t)
    four = frozenset(
        {
            LiquidApp(Name("<=", 0), [LiquidVar(x), LiquidLiteralInt(10)]),
            LiquidApp(Name(">=", 0), [LiquidVar(x), LiquidLiteralInt(0)]),
            LiquidApp(Name("!=", 0), [LiquidVar(x), LiquidLiteralInt(5)]),
            LiquidApp(Name("==", 0), [LiquidVar(x), LiquidLiteralInt(3)]),
        }
    )
    quads = bool_quad_conjunctions(ctx, four, max_singles=12, max_quads=24)
    assert len(quads) >= 1
    assert all(_and_chain_depth(t) >= 3 for t in quads)
