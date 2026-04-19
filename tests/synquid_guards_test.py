from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.terms import Annotation, Application, Var
from aeon.core.types import TypeConstructor
from aeon.synthesis.modules.synquid.guards import bool_pairwise_conjunctions, bool_terms_from_qualifier_atoms
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
