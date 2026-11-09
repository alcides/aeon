"""Constructor polymorphism through class dictionaries and generic callers."""

import pytest

from tests.typeclass_test import _errors, _run


FUNCTOR = """
inductive Box a
| box (value:a) : (Box a)
class Functor (f : B -> B) where
    fmap : forall a:B, forall b:B, (g:(x:a) -> b) -> (xs:(f a)) -> (f b);
instance : Functor Box where
    fmap g xs := match xs with | box x => Box.box (g x);
"""


def test_functor_infers_constructor_and_both_element_types():
    assert (
        _run(
            FUNCTOR
            + """
    def main (args:Int) : Bool :=
        match fmap (fun x => x > 2) (Box.box 4) with | box v => v;
    """
        )
        is True
    )


def test_generic_function_passes_higher_kinded_dictionary():
    assert (
        _run(
            FUNCTOR
            + """
    def increment [Functor f] (xs:(f Int)) : (f Int) := fmap (fun x => x + 1) xs;
    def main (args:Int) : Int := match increment (Box.box 4) with | box v => v;
    """
        )
        == 5
    )


def test_higher_kinded_superclass():
    assert (
        _run(
            FUNCTOR
            + """
    class Pointed (f : B -> B) extends (Functor f) where
        point : forall a:B, (x:a) -> (f a);
    instance : Pointed Box where
        point x := Box.box x;
    def increment [Pointed f] (xs:(f Int)) : (f Int) := fmap (fun x => x + 1) xs;
    def main (args:Int) : Int := match increment (Box.box 4) with | box v => v;
    """
        )
        == 5
    )


def test_constructor_arguments_can_be_partial_applications():
    assert (
        _run("""
    inductive Pair a b
    | pair (first:a) (second:b) : (Pair a b)
    class Functor (f : B -> B) where
        fmap : forall a:B, forall b:B, (g:(x:a) -> b) -> (xs:(f a)) -> (f b);
    instance : Functor (Pair Int) where
        fmap g xs := match xs with | pair x y => Pair.pair x (g y);
    def main (args:Int) : Int :=
        match fmap (fun x => x + 1) (Pair.pair 9 4) with | pair x y => y;
    """)
        == 5
    )


@pytest.mark.parametrize("argument", ["Int", "(Box Int)"])
def test_saturated_type_is_not_a_constructor_argument(argument):
    assert _errors(
        FUNCTOR
        + f"""
    def main (args:Int) : Int := fmap{{{argument}}} (fun x => x + 1) (Box.box 4);
    """
    )


def test_method_implementation_must_be_parametric():
    assert _errors(FUNCTOR.replace("Box.box (g x)", "Box.box 0") + "def main (args:Int) : Int := 0;")


def test_monad_example_runs():
    from pathlib import Path

    source = Path("examples/syntax/higher_kinded_typeclasses.ae").read_text()
    assert _run(source) == 7


def test_imported_higher_kinded_class(tmp_path, monkeypatch):
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI

    (tmp_path / "BoxFunctor.ae").write_text(FUNCTOR)
    main = tmp_path / "main.ae"
    main.write_text("""
    open BoxFunctor
    def main (args:Int) : Int := match fmap (fun x => x + 1) (Box.box 4) with | box x => x;
    """)
    monkeypatch.chdir(tmp_path)
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not list(driver.parse(filename=str(main)))
    assert driver.run() == 5


def test_core_rejects_constructor_used_as_a_value_type():
    from aeon.core.types import ArrowKind, Kind, TypeConstructor, TypeVar, t_int
    from aeon.typechecking.context import TypingContext
    from aeon.typechecking.well_formed import wellformed
    from aeon.utils.name import Name

    f = Name("f", 1)
    ctx = TypingContext().with_typevar(f, ArrowKind(Kind.BASE, Kind.BASE))
    assert not wellformed(ctx, TypeVar(f))
    assert wellformed(ctx, TypeVar(f), ArrowKind(Kind.BASE, Kind.BASE))
    assert wellformed(ctx, TypeConstructor(f, [t_int]))
    assert not wellformed(ctx, TypeConstructor(f, [t_int, t_int]))


def test_constructor_substitution_respects_shadowing():
    from aeon.core.instantiation import type_substitution
    from aeon.core.types import ArrowKind, Kind, TypeConstructor, TypePolymorphism, t_int
    from aeon.utils.name import Name

    f, box = Name("f", 1), Name("Box", 2)
    application = TypeConstructor(f, [t_int])
    assert type_substitution(application, f, TypeConstructor(box)) == TypeConstructor(box, [t_int])
    poly = TypePolymorphism(f, ArrowKind(Kind.BASE, Kind.BASE), application)
    assert type_substitution(poly, f, TypeConstructor(box)) == poly


def test_polymorphic_default_method():
    source = FUNCTOR.replace(
        "instance : Functor Box where",
        """    keep : forall a:B, (xs:(f a)) -> (f a) := fun xs => fmap (fun x => x) xs;
        instance : Functor Box where""",
    )
    assert (
        _run(
            source
            + """
    def main (args:Int) : Int := match keep (Box.box 9) with | box x => x;
    """
        )
        == 9
    )


def test_instance_with_higher_kinded_prerequisite():
    assert (
        _run(
            FUNCTOR
            + """
    class Mapper (f:B -> B) where
        transform : forall a:B, forall b:B, (g:(x:a) -> b) -> (xs:(f a)) -> (f b);
    instance [Functor f] : Mapper f where
        transform g xs := fmap g xs;
    def main (args:Int) : Bool := match transform (fun x => x > 2) (Box.box 4) with | box x => x;
    """
        )
        is True
    )


def test_constructor_variable_in_instance_head():
    assert (
        _run(
            FUNCTOR
            + """
    class Sized (a:B) where
        size : (x:a) -> Int;
    instance [Functor f] : Sized (f Int) where
        size x := 1;
    def main (args:Int) : Int := size (Box.box 4);
    """
        )
        == 1
    )


def test_constructor_variable_overlap_is_rejected():
    from aeon.errors import TypeClassError

    errors = _errors(
        FUNCTOR
        + """
    class Sized (a:B) where
        size : (x:a) -> Int;
    instance [Functor f] : Sized (f Int) where
        size x := 1;
    instance : Sized (Box Int) where
        size x := 2;
    def main (args:Int) : Int := 0;
    """
    )
    assert any(isinstance(e, TypeClassError) and "Overlapping" in str(e) for e in errors)


def test_constructor_kinds_follow_context_shadowing():
    from aeon.core.types import ArrowKind, Kind, TypeConstructor, t_int, t_set
    from aeon.typechecking.context import TypingContext, TypeConstructorBinder
    from aeon.typechecking.well_formed import wellformed
    from aeon.utils.name import Name

    # The generic Set library shadows the nullary built-in Set declaration.
    ctx = TypingContext([TypeConstructorBinder(t_set.name, [Name("a", 1)])])
    assert ctx.kind_of(t_set) == ArrowKind(Kind.BASE, Kind.BASE)
    assert wellformed(ctx, TypeConstructor(t_set.name, [t_int]))
