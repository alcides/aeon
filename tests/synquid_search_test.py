from aeon.core.terms import Application, Literal, Var
from aeon.core.types import TypeConstructor
from aeon.synthesis.modules.synquid.search import sorted_level_candidates, term_size
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

_INT = TypeConstructor(Name("Int", 0), [])


def test_term_size_counts_nodes():
    x = Var(Name("x", 0))
    lit = Literal(1, _INT)
    app = Application(Application(Var(Name("<=", 0)), x), lit)
    assert term_size(x) == 1
    assert term_size(lit) == 1
    assert term_size(app) >= 3


def test_sorted_level_candidates_orders_by_term_size():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    large = Application(
        Application(Var(Name("+", 0)), Literal(1, _INT)),
        Literal(2, _INT),
    )
    small = Literal(0, _INT)
    assert term_size(large) > term_size(small)
    mem: dict = {(ctx, 0, _INT): [large, small]}
    ordered = list(sorted_level_candidates(ctx, 0, _INT, skip, mem))
    assert ordered == [small, large]
