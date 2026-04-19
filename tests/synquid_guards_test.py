from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Annotation, Application, Var
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
    x = Name("x", 0)
    int_t = TypeConstructor(Name("Int", 0), [])
    ctx = TypingContext().with_var(x, int_t)
    one = frozenset({LiquidApp(Name("<=", 0), [LiquidVar(x), LiquidLiteralInt(1)])})
    assert bool_pairwise_conjunctions(ctx, one) == []
    two = frozenset(
        {
            LiquidApp(Name("<=", 0), [LiquidVar(x), LiquidLiteralInt(10)]),
            LiquidApp(Name(">=", 0), [LiquidVar(x), LiquidLiteralInt(0)]),
        }
    )
    singles = bool_terms_from_qualifier_atoms(ctx, two)
    assert len(singles) >= 2
    pairs = bool_pairwise_conjunctions(ctx, two, max_singles=12, max_pairs=24)
    assert len(pairs) >= 1
    assert all(_is_and_annotation(p) for p in pairs)


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
