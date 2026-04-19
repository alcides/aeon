from itertools import islice

from aeon.core.terms import Abstraction, Literal
from aeon.core.types import AbstractionType, TypeConstructor
from aeon.synthesis.modules.synquid.engine import synthes_memory
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

_INT = TypeConstructor(Name("Int", 0), [])
_STR = TypeConstructor(Name("String", 0), [])


def test_synthes_memory_string_literals():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    xs = list(islice(synthes_memory(ctx, 0, _STR, skip, {}), 20))
    assert xs
    assert all(isinstance(t, Literal) for t in xs)
    assert all(t.type == _STR for t in xs)


def test_synthes_memory_abstraction_goal_emits_lambda():
    ctx = TypingContext()
    goal = AbstractionType(Name("x", 0), _INT, _INT)

    def skip(_: Name) -> bool:
        return False

    mem: dict = {}
    sample = list(islice(synthes_memory(ctx, 1, goal, skip, mem), 400))
    assert any(isinstance(t, Abstraction) for t in sample)
