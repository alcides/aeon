"""Dictionary specialization is shared, kind-correct and checked after expansion."""

from pathlib import Path
from time import monotonic

import pytest

from aeon.backend.evaluator import eval as aeon_eval
from aeon.core.substitutions import substitution
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, TypePolymorphism
from aeon.core.types import ArrowKind, Kind, TypeConstructor, TypeVar, t_bool, t_int, top
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.entrypoint import synthesize_holes
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.joint import JointCandidate, JointSynthesizer
from aeon.synthesis.identification import get_holes_info, incomplete_functions_and_holes, term_has_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.typeclasses import DictionaryResolver, match_types, prepare_typeclass_components, type_universe
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.context import TypeConstructorBinder, TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


CONVERT = Path("examples/synthesis/typeclasses/convert.ae").read_text()


def parse(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not list(driver.parse(aeon_code=source))
    return driver


def solve(driver, backend, budget=5):
    with driver.session.activate():
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
            driver.metadata,
            make_synthesizer(backend),
            budget,
            SilentSynthesisUI(),
        )
        completed = driver.core
        for name, value in mapping.items():
            assert value is not None
            assert "_method_" not in repr(value)
            completed = substitution(completed, value, name)
        assert not term_has_holes(completed)
        assert check_type(driver.typing_ctx, completed, top)
        return aeon_eval(completed, driver.evaluation_ctx)


def hole(driver):
    targets = incomplete_functions_and_holes(driver.typing_ctx, driver.core)
    info = get_holes_info(driver.typing_ctx, driver.core, top, targets, refined_types=True)
    return next(iter(info.values())), frozenset(f for f, _ in targets)


@pytest.mark.parametrize(
    "backend",
    [
        "tdsyn",
        "tdsyn_backward",
        "tdsyn_random",
        "synquid",
        "fta",
        "afta",
        "lta",
        "cata",
        "enumerative",
        "random_search",
        "gp",
    ],
)
def test_generic_convert_across_backends(backend, monkeypatch):
    monkeypatch.setenv("AEON_SEED", "0")
    assert solve(parse(CONVERT), backend) is True


def test_kind_matching_includes_abstract_and_partially_applied_constructors():
    pair, f, a = Name("Pair"), Name("f"), Name("a")
    ctx = TypingContext([TypeConstructorBinder(pair, [Name("x"), Name("y")])])
    ctx = ctx.with_typevar(f, ArrowKind(Kind.BASE, Kind.BASE)).with_typevar(a, Kind.BASE)
    actual = TypeConstructor(pair, [t_int, t_bool])
    universe = type_universe(ctx, actual)
    assert TypeConstructor(pair, [t_int]) in universe
    assert TypeVar(f) in universe and TypeVar(a) in universe
    subst = {}
    assert match_types(
        ctx, TypeConstructor(f, [TypeVar(a)]), actual, {f: ArrowKind(Kind.BASE, Kind.BASE), a: Kind.BASE}, subst
    )
    assert subst == {f: TypeConstructor(pair, [t_int]), a: t_bool}
    assert not match_types(ctx, TypeVar(f), t_int, {f: ArrowKind(Kind.BASE, Kind.BASE)}, {})
    assert not match_types(ctx, TypeConstructor(pair, [TypeVar(a), TypeVar(a)]), actual, {a: Kind.BASE}, {})


def test_specializations_keep_distinct_names_and_only_checked_dictionaries():
    driver = parse(CONVERT)
    with driver.session.activate():
        (goal, ctx), exclude = hole(driver)
        prepared = prepare_typeclass_components(ctx, goal, exclude=exclude, deadline=monotonic() + 5)
        assert prepared.definitions
        assert len({n.name for n in prepared.definitions}) == len(prepared.definitions)
        for name, value in prepared.definitions.items():
            assert check_type(ctx, value, prepared.context.type_of(name))


def test_unregistered_datatypes_are_not_dictionary_constraints():
    driver = parse("""
    inductive Box a | box (x:a) : (Box a)
    def unbox (x:(Box Int)) : Int := match x with | box n => n;
    def result (x:(Box Int)) : Int := ?body;
    def main (args:Int) : Int := result (Box.box 4);
    """)
    (goal, ctx), exclude = hole(driver)
    prepared = prepare_typeclass_components(ctx, goal, exclude=exclude)
    assert not prepared.definitions
    assert prepared.context is ctx


def test_missing_instance_is_not_fabricated_from_dictionary_constructor():
    driver = parse("""
    class Eq (a:B) where eq : (x:a) -> (y:a) -> Bool;
    def result (x:Int) : Bool := ?body;
    def main (args:Int) : Bool := result 4;
    """)
    with driver.session.activate():
        (goal, ctx), exclude = hole(driver)
        resolver = DictionaryResolver(ctx, type_universe(ctx, goal))
        cls = next(iter(resolver.classes))
        assert resolver.resolve(TypeConstructor(cls, [t_int])) is None
        assert not prepare_typeclass_components(ctx, goal, exclude=exclude).definitions


@pytest.mark.parametrize("backend", ["tdsyn", "tdsyn_backward", "synquid"])
def test_higher_kinded_method_uses_scoped_constructor_variable(backend):
    driver = parse("""
    inductive Box a | box (x:a) : (Box a)
    class Pointed (f:B -> B) where pure : forall a:B, (x:a) -> (f a);
    instance : Pointed Box where pure x := Box.box x;
    def wrap [Pointed f] (x:a) : (f a) := ?body;
    def main (args:Int) : Int := match wrap{Int}{Box} 7 with | box x => x;
    """)
    assert solve(driver, backend, budget=10) == 7


def test_superclass_and_recursive_instance_resolution():
    driver = parse("""
    inductive Box a | box (x:a) : (Box a)
    class Eq (a:B) where eq : (x:a) -> (y:a) -> Bool;
    class Order (a:B) extends (Eq a) where lt : (x:a) -> (y:a) -> Bool;
    instance : Eq Int where eq x y := x = y;
    instance [Eq a] : Eq (Box a) where
        eq x y := eq (Box_rec x (fun v => v)) (Box_rec y (fun v => v));
    def result [Order a] (x:a) : Bool := ?body;
    def main (args:Int) : Int := 0;
    """)
    with driver.session.activate():
        (goal, ctx), _ = hole(driver)
        resolver = DictionaryResolver(ctx, type_universe(ctx, goal))
        eq = next(n for n in resolver.classes if n.name == "Eq")
        box = next(e.name for e in ctx._constructor_entries() if e.name.name == "Box")
        abstract = TypeVar(ctx.typevars()[0][0])
        for target in (
            TypeConstructor(eq, [abstract]),
            TypeConstructor(eq, [TypeConstructor(box, [TypeConstructor(box, [t_int])])]),
        ):
            evidence = resolver.resolve(target)
            assert evidence is not None
            assert check_type(ctx, evidence, target)


@pytest.mark.parametrize("backend", ["amaze", "arborist", "tdsyn", "fta", "afta"])
def test_scalar_grammars_can_use_checked_typeclass_calls(backend):
    driver = parse("""
    class Squares (a:B) where
        sumSquares : (x:a) -> (y:a) -> {r:a | r = x * x + y * y};
    instance : Squares Int where
        sumSquares x y := x * x + y * y;
    def norm (x:Int) (y:Int) : {r:Int | r = x * x + y * y} := ?body;
    def main (args:Int) : {r:Int | r = 25} := norm 3 4;
    """)
    assert solve(driver, backend, budget=10) == 25


@pytest.mark.parametrize(
    "global_instance", ["instance : Eq Int where eq x y := x = y;", "instance : Eq a where eq x y := true;"]
)
def test_given_superclass_precedes_global_instance(global_instance):
    driver = parse(
        """
    class Eq (a:B) where eq : (x:a) -> (y:a) -> Bool;
    class Order (a:B) extends (Eq a) where lt : (x:a) -> (y:a) -> Bool;
    GLOBAL_INSTANCE
    instance : Order Int where lt x y := x < y;
    def result [Order Int] (x:Int) : Bool := ?body;
    def main (args:Int) : Bool := result 4;
    """.replace("GLOBAL_INSTANCE", global_instance)
    )
    with driver.session.activate():
        (goal, ctx), _ = hole(driver)
        order = next(e.name for e in ctx._constructor_entries() if e.name.name == "Order")
        eq = next(e.name for e in ctx._constructor_entries() if e.name.name == "Eq")
        local = next(n for n, t in reversed(ctx.concrete_vars()) if t == TypeConstructor(order, [t_int]))
        resolver = DictionaryResolver(ctx, type_universe(ctx, goal), given=frozenset({local}))
        evidence = resolver.resolve(TypeConstructor(eq, [t_int]))
        assert evidence is not None and repr(local) in repr(evidence)
        assert "__super_Order" in repr(evidence)


def test_growing_instance_requirements_terminate_without_fabricating_evidence():
    cls, box, a = Name("C"), Name("Box"), Name("a")
    ctx = TypingContext(
        [
            TypeConstructorBinder(cls, [a], is_typeclass=True),
            TypeConstructorBinder(box, [a]),
        ]
    )
    provider = TypePolymorphism(
        a,
        Kind.BASE,
        AbstractionType(
            Name("d"),
            TypeConstructor(cls, [TypeConstructor(box, [TypeVar(a)])]),
            TypeConstructor(cls, [TypeVar(a)]),
        ),
    )
    ctx = ctx.with_var(Name("grow"), provider)
    assert DictionaryResolver(ctx, (t_int,)).resolve(TypeConstructor(cls, [t_int])) is None


def test_shared_validator_and_fitness_expand_components():
    driver = parse("""
    class Squares (a:B) where sumSquares : (x:a) -> {r:a | r = x * x};
    instance : Squares Int where sumSquares x := x * x;
    @minimize_int(square 7)
    def square (x:Int) : {r:Int | r = x * x} := ?body;
    def main (args:Int) : Int := square 7;
    """)

    class Inspect(Synthesizer):
        def synthesize(self, ctx, type, validate, evaluate, fun_name, metadata, **kwargs):
            candidates = [
                Var(n)
                for n, ty in ctx.concrete_vars()
                if n.name.startswith("_method_sumSquares") and not isinstance(ty, AbstractionType)
            ]
            candidate = next(t for t in candidates if validate(t))
            assert evaluate(candidate) == [49.0]
            return candidate

    with driver.session.activate():
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
            driver.metadata,
            Inspect(),
            5,
            SilentSynthesisUI(),
        )
    assert mapping and all("_method_" not in repr(t) for t in mapping.values())


def test_joint_candidates_expand_each_holes_own_dictionaries():
    driver = parse(CONVERT.replace("def main", "def again [Convert a b] (x:a) : b := ?second;\ndef main"))

    class Inspect(JointSynthesizer):
        def synthesize_joint(self, holes, validate, evaluate, fun_name, metadata, budget, ui):
            candidate = JointCandidate(
                tuple(
                    Var(
                        next(
                            n for n, t in h.ctx.concrete_vars() if n.name.startswith("_method_convert") and t == h.type
                        )
                    )
                    for h in holes
                )
            )
            assert validate(candidate)
            return candidate

    with driver.session.activate():
        mapping = synthesize_holes(
            driver.typing_ctx,
            driver.evaluation_ctx,
            driver.core,
            incomplete_functions_and_holes(driver.typing_ctx, driver.core),
            driver.metadata,
            Inspect(),
            5,
            SilentSynthesisUI(),
        )
    assert len(mapping) == 2 and all("_method_" not in repr(t) for t in mapping.values())


def test_imported_class_identity_survives_linking():
    driver = parse("""
    open Num
    def twice [Num a] (x:a) : {r:a | r = x + x} := ?body;
    def main (args:Int) : {r:Int | r = 10} := twice 5;
    """)
    assert solve(driver, "tdsyn") == 10


def test_partial_constructor_instance_produces_a_checked_callable():
    driver = parse("""
    inductive Pair a b | pair (first:a) (second:b) : (Pair a b)
    class Pointed (f:B -> B) where pure : forall a:B, (x:a) -> (f a);
    instance : Pointed (Pair Int) where pure x := Pair.pair 0 x;
    def wrap (x:Bool) : (Pair Int Bool) := ?body;
    def main (args:Int) : Bool := match wrap true with | pair first flag => flag;
    """)
    with driver.session.activate():
        (goal, ctx), exclude = hole(driver)
        components = prepare_typeclass_components(ctx, goal, exclude=exclude, deadline=monotonic() + 5)
        name = next(
            n for n, t in components.context.concrete_vars() if n.name.startswith("_method_pure_") and t == goal
        )
        candidate = components.expand(Var(name))
        assert check_type(ctx, candidate, goal)
        target = incomplete_functions_and_holes(driver.typing_ctx, driver.core)[0][1][0]
        completed = substitution(driver.core, candidate, target)
        assert not term_has_holes(completed)
        assert aeon_eval(completed, driver.evaluation_ctx) is True


def test_shadowed_method_is_not_reintroduced_by_specialization():
    driver = parse(CONVERT.replace(":= ?body;", ":= let convert := unit in ?body;"))
    with driver.session.activate():
        (goal, ctx), exclude = hole(driver)
        components = prepare_typeclass_components(ctx, goal, exclude=exclude, deadline=monotonic() + 5)
        assert not any(n.name.startswith("_method_convert_") for n in components.definitions)
