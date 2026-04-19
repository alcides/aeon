from aeon.core.terms import Application, Literal, Var
from aeon.core.types import TypeConstructor
from aeon.synthesis.modules.synquid.search import term_size
from aeon.utils.name import Name

_INT = TypeConstructor(Name("Int", 0), [])


def test_term_size_counts_nodes():
    x = Var(Name("x", 0))
    lit = Literal(1, _INT)
    app = Application(Application(Var(Name("<=", 0)), x), lit)
    assert term_size(x) == 1
    assert term_size(lit) == 1
    assert term_size(app) >= 3
