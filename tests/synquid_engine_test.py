from itertools import islice

from aeon.core.terms import Abstraction, Application, Literal, TypeApplication, Var
from aeon.core.types import AbstractionType, TypeConstructor, TypePolymorphism, TypeVar, Kind
from aeon.synthesis.modules.synquid.engine import _eliminations, _peel_polymorphism, _uncurry_arrow_b, synthes_memory
from aeon.synthesis.modules.synquid.round_trip import match_result
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

_INT = TypeConstructor(Name("Int", 0), [])
_STR = TypeConstructor(Name("String", 0), [])
_UNIT = TypeConstructor(Name("Unit", 0), [])


def test_synthes_memory_string_literals():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    xs = list(islice(synthes_memory(ctx, 0, _STR, skip, {}), 20))
    assert xs
    assert all(isinstance(t, Literal) for t in xs)
    assert all(t.type == _STR for t in xs)


def test_synthes_memory_unit_literal():
    ctx = TypingContext()

    def skip(_: Name) -> bool:
        return False

    xs = list(islice(synthes_memory(ctx, 0, _UNIT, skip, {}), 5))
    assert any(isinstance(t, Literal) and t.type == _UNIT for t in xs)


def test_synthes_memory_typevar_from_context():
    tv = TypeVar(Name("t", 0))
    x = Name("x", 0)
    ctx = TypingContext().with_typevar(tv.name, Kind.BASE).with_var(x, tv)

    def skip(_: Name) -> bool:
        return False

    terms = list(islice(synthes_memory(ctx, 0, tv, skip, {}), 10))
    assert Var(x) in terms


def _operator_name(term):
    while isinstance(term, (Application, TypeApplication)):
        term = term.fun if isinstance(term, Application) else term.body
    return term.name.name if isinstance(term, Var) else None


def test_eliminations_do_not_apply_arithmetic_at_list_goals(monkeypatch):
    """``+`` is ``forall a. a -> a -> a``, so a list goal used to instantiate it."""
    produced = []

    def record(ctx, level, head, application, skip, mem, filling=False):
        produced.append(head)
        yield Application(head, Var(Name("arg", 0)))

    monkeypatch.setattr("aeon.synthesis.modules.synquid.engine._application_terms", record)
    parameter = Name("a", 0)
    poly = TypePolymorphism(
        parameter,
        Kind.BASE,
        AbstractionType(
            Name("x", 0), TypeVar(parameter), AbstractionType(Name("y", 0), TypeVar(parameter), TypeVar(parameter))
        ),
    )
    list_t = TypeConstructor(Name("List", 0), [])
    ctx = TypingContext()
    for op in ("+", "-", "*", "/"):
        ctx = ctx.with_var(Name(op, 0), poly)
    tyvars, inner = _peel_polymorphism(poly)
    _params, result = _uncurry_arrow_b(inner)
    assert match_result(result, list_t, set(tyvars)) is not None

    yielded = list(_eliminations(ctx, 1, list_t, lambda _name: False, {}))
    assert all(_operator_name(term) not in {"+", "-", "*", "/"} for term in yielded)
    assert all(_operator_name(term) not in {"+", "-", "*", "/"} for term in produced)


def test_synthes_memory_abstraction_goal_emits_lambda():
    ctx = TypingContext()
    goal = AbstractionType(Name("x", 0), _INT, _INT)

    def skip(_: Name) -> bool:
        return False

    mem: dict = {}
    sample = list(islice(synthes_memory(ctx, 1, goal, skip, mem), 400))
    assert any(isinstance(t, Abstraction) for t in sample)
