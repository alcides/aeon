"""Generated semantic invariants; failures shrink to small reproducible programs."""

from __future__ import annotations

from itertools import islice
from pathlib import Path
from tempfile import TemporaryDirectory
from typing import Any

from hypothesis import given, strategies as st

from aeon.backend.evaluator import EvaluationContext, eval as evaluate
from aeon.compilation.compile import compile_program
from aeon.compilation.session import CompilationSession
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.substitutions import substitution
from aeon.core.terms import Abstraction, Application, Literal, Var, Rec, Let, Term
from aeon.core.types import AbstractionType, Kind, RefinedType, t_int, t_bool
from aeon.elaboration.instantiation import type_substitution, type_variable_instantiation
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.sugar.stypes import STypePolymorphism, STypeVar, STypeConstructor
from aeon.synthesis.modules.enumerative import iter_candidates
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Implication, LiquidConstraint

integers = st.integers(min_value=-20, max_value=20)
expressions = st.recursive(
    st.one_of(integers, st.just("variable")),
    lambda child: st.tuples(st.sampled_from(["+", "-", "*"]), child, child),
    max_leaves=6,
)


@st.composite
def bound_terms(draw: Any) -> Term:
    """Use compiler-style unique binder identities, not raw shadowed spellings."""
    next_id = 100
    free = [Name("free", index) for index in range(3)]

    def build(depth: int, scope: list[Name]) -> Term:
        nonlocal next_id
        kind = draw(st.sampled_from(["var", "literal"] if depth == 0 else ["var", "literal", "lambda", "let", "app"]))
        if kind == "var":
            return Var(draw(st.sampled_from(free + scope)))
        if kind == "literal":
            return Literal(draw(integers), t_int)
        if kind == "app":
            return Application(build(depth - 1, scope), build(depth - 1, scope))
        binder = Name("bound", next_id)
        next_id += 1
        if kind == "lambda":
            return Abstraction(binder, build(depth - 1, [*scope, binder]))
        return Let(binder, build(depth - 1, scope), build(depth - 1, [*scope, binder]))

    return build(3, [])


def free_variables(term: Term) -> set[Name]:
    """Independent small-subset oracle for the substitution property."""
    match term:
        case Var(name):
            return {name}
        case Literal():
            return set()
        case Abstraction(name, body):
            return free_variables(body) - {name}
        case Application(fun, arg):
            return free_variables(fun) | free_variables(arg)
        case Let(name, value, body):
            return free_variables(value) | (free_variables(body) - {name})
        case _:
            raise AssertionError(f"Unsupported generated term: {term}")


@given(bound_terms(), st.integers(min_value=0, max_value=2), st.integers(min_value=0, max_value=2))
def test_substitution_preserves_free_variable_accounting(term: Term, target_id: int, replacement_id: int):
    target, replacement = Name("free", target_id), Name("free", replacement_id)
    before = free_variables(term)
    expected_free = before - {target}
    if target in before:
        expected_free.add(replacement)
    assert free_variables(substitution(term, Var(replacement), target)) == expected_free


def render(expression: Any, variable: str = "x") -> str:
    if expression == "variable":
        return variable
    if isinstance(expression, int):
        return f"({expression})"
    operator, left, right = expression
    return f"({render(left, variable)} {operator} {render(right, variable)})"


def expected(expression: Any, value: int) -> int:
    if expression == "variable":
        return value
    if isinstance(expression, int):
        return expression
    operator, left, right = expression
    a, b = expected(left, value), expected(right, value)
    return {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b}[operator]()


def driver(source: str) -> AeonDriver:
    result = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0, no_main=True))
    assert not list(result.parse(aeon_code=source, filename="<stdin>"))
    return result


@given(expressions, integers, st.integers(min_value=1, max_value=10000))
def test_substitution_commutes_with_beta_evaluation(expression: Any, value: int, binder_id: int):
    binder = Name("x", binder_id)
    literal = Literal(value, t_int)

    def core(node: Any) -> Term:
        if node == "variable":
            return Var(binder)
        if isinstance(node, int):
            return Literal(node, t_int)
        operator, left, right = node
        return Application(Application(Var(Name(operator, 0)), core(left)), core(right))

    # Same spelling, different binder identity: substituting the outer x must
    # still reach its occurrences beneath this inner binding.
    body = Let(Name("x", binder_id + 1), Literal(value + 1, t_int), core(expression))
    context = EvaluationContext(
        {
            Name("+", 0): lambda a: lambda b: a + b,
            Name("-", 0): lambda a: lambda b: a - b,
            Name("*", 0): lambda a: lambda b: a * b,
        }
    )
    replacement = substitution(body, literal, binder)
    assert (
        evaluate(Application(Abstraction(binder, body), literal), context)
        == evaluate(replacement, context)
        == expected(expression, value)
    )


@given(st.sampled_from(["X", "Element", "Value"]), st.integers(min_value=0, max_value=10000))
def test_type_substitution_does_not_capture_free_variables(spelling: str, binder_id: int):
    bound, target = Name(spelling, binder_id), Name("target", binder_id + 1)
    original = STypePolymorphism(bound, Kind.BASE, STypeVar(target))
    for substitute in (type_substitution, type_variable_instantiation):
        result = substitute(original, target, STypeVar(bound))
        assert isinstance(result, STypePolymorphism)
        assert isinstance(result.body, STypeVar)
        assert result.body.name == bound
        assert result.name != bound


def test_type_binder_allocation_avoids_existing_free_and_bound_names(monkeypatch):
    from aeon.utils.name import fresh_counter

    bound, nested, free, target = Name("X", 1), Name("X", 2), Name("X", 3), Name("target", 4)
    original = STypePolymorphism(bound, Kind.BASE, STypePolymorphism(nested, Kind.BASE, STypeVar(target)))
    replacement = STypeConstructor(Name("Pair", 0), [STypeVar(bound), STypeVar(free)])
    for substitute in (type_substitution, type_variable_instantiation):
        ids = iter([1, 2, 3, 5])
        monkeypatch.setattr(fresh_counter, "fresh", lambda: next(ids))
        result = substitute(original, target, replacement)
        assert isinstance(result, STypePolymorphism)
        assert result.name == Name("X", 5)
        assert isinstance(result.body, STypePolymorphism)
        assert result.body.name == nested
        assert result.body.body == replacement


@given(integers, integers, st.integers(min_value=1, max_value=10000))
def test_alpha_renaming_preserves_refinement_proofs(lower: int, upper: int, binder_id: int):
    results = []
    for name in (Name("x", 0), Name("renamed", binder_id)):
        constraint = Implication(
            name,
            t_int,
            LiquidApp(Name(">=", 0), [LiquidVar(name), LiquidLiteralInt(lower)]),
            LiquidConstraint(LiquidApp(Name(">=", 0), [LiquidVar(name), LiquidLiteralInt(upper)])),
        )
        with CompilationSession().activate():
            results.append(smt_valid(constraint))
    assert results == [lower >= upper] * 2


@given(expressions, integers, st.sampled_from(["arg", "count", "value"]))
def test_alpha_renaming_preserves_typing_and_evaluation(expression: Any, value: int, renamed: str):
    results = []
    for parameter in ("x", renamed):
        source = (
            f"def f ({parameter}:Int) : Int := {render(expression, parameter)}; def main (u:Int) : Int := f ({value});"
        )
        results.append(driver(source).run())
    assert results == [expected(expression, value)] * 2


@given(expressions, integers)
def test_interpreter_python_and_llvm_agree(expression: Any, value: int):
    body = render(expression)
    source = f"def f (x:Int) : Int := {body}; def main (u:Int) : Int := f ({value});"
    interpreted = driver(source)
    namespace: dict[str, Any] = {}
    exec(interpreted.export("f"), namespace)
    llvm = driver("@llvm\n" + source)
    assert interpreted.run() == namespace["f"](value) == llvm.run() == expected(expression, value)


@given(integers)
def test_cached_and_uncached_compilation_have_the_same_interface(value: int):
    source = f"def value : Int := ({value});"
    with TemporaryDirectory(prefix="aeon-cache-property-") as directory, CompilationSession().activate():
        path = str(Path(directory) / "Unit.ae")
        first, errors = compile_program(source, filename=path, write_cache=False)
        assert not errors
        cached, errors = compile_program(source, filename=path, write_cache=False)
        assert not errors
        assert cached is first
        fresh, errors = compile_program(source, filename=path, use_cache=False, write_cache=False)
        assert not errors
        assert set(cached.exports) == set(fresh.exports)
        assert cached.exports["value"].core_type == fresh.exports["value"].core_type
        assert isinstance(cached.core_spine, Rec) and isinstance(fresh.core_spine, Rec)
        assert evaluate(cached.core_spine.var_value, EvaluationContext()) == value
        assert evaluate(fresh.core_spine.var_value, EvaluationContext()) == value


@given(integers)
def test_synthesized_candidates_are_independently_rechecked(value: int):
    binder = Name("result", 0)
    target = RefinedType(binder, t_int, LiquidApp(Name("==", 0), [LiquidVar(binder), LiquidLiteralInt(value)]))
    equality = AbstractionType(Name("left", 2), t_int, AbstractionType(Name("right", 3), t_int, t_bool))
    context = TypingContext([]).with_var(Name("==", 0), equality)
    with CompilationSession().activate():
        candidates = list(islice(iter_candidates(context, target, Name("synth", 1), {}), 1))
    assert candidates, "Required deterministic synthesis must find an exact integer"
    with CompilationSession().activate():
        for candidate in candidates:
            assert check_type(context, candidate, target)
            assert evaluate(candidate) == value
