"""Resource wrappers never manufacture a second owner of the same handle."""

import pytest

from aeon.errors import LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def compile_source(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    return driver, list(driver.parse(aeon_code=source))


@pytest.mark.parametrize(
    "source",
    [
        """import Array; open ForkJoin;
       def bad (1 token:(Halves Int)):Unit :=
           let 1 a := ForkJoin.half_left token in
           let 1 b := ForkJoin.half_left token in
           let _ := Array.dispose a in Array.dispose b;""",
        """open Reader;
       def bad (1 token:ReaderStep):Unit :=
           let 1 a := Reader.read_reader token in
           let 1 b := Reader.read_reader token in
           let _ := Reader.close a in Reader.close b;""",
        """open Random;
       def bad (1 token:Draw):Unit :=
           let 1 a := Random.draw_next token in
           let 1 b := Random.draw_next token in
           let _ := Random.close_rng a in Random.close_rng b;""",
        """open DataFrame;
       def bad (1 token:DataFramePair):Unit :=
           let 1 a := DataFrame.fst_df token in
           let 1 b := DataFrame.fst_df token in
           let _ := DataFrame.dispose a in DataFrame.dispose b;""",
        """open LearningCore;
       def bad (1 token:DatasetPair):Unit :=
           let 1 a := LearningCore.train_of token in
           let 1 b := LearningCore.train_of token in
           let _ := LearningCore.dispose_dataset a in LearningCore.dispose_dataset b;""",
    ],
)
def test_owned_projection_cannot_be_repeated(source):
    _, errors = compile_source(source)
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_array_update_reuses_owned_storage():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
        import Array;
        def storage_id (borrow arr:(Array Int)):Int := native "id(arr)";
        def main (_:Int):Bool :=
            let 1 arr := #[1,2] in
            let before := storage_id arr in
            let 1 updated := Array.set arr 0 7 in
            let same := before = storage_id updated in
            let value := Array.get updated 0 in
            let _ := Array.dispose updated in
            same && value = 7;
    """
        )
    )
    assert not errors, errors
    assert driver.run() is True


def test_borrowed_stack_observations_keep_the_owner():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
        import Stack;
        def main (_:Int):Int :=
            let 1 stack := Stack.push 7 (Stack.new_stack{Int} unit) in
            let size := Stack.length stack in
            let top := Stack.peek stack in
            Stack.with_pop (Stack.pop stack) (fun value => fun empty =>
                let _ := Stack.discard empty in size + top + value);
    """
        )
    )
    assert not errors, errors
    assert driver.run() == 15


def test_nested_array_elements_can_be_moved_without_copy():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
        import Array;
        def main (_:Int):Int :=
            let 1 outer := #[#[3,4]] in
            let 1 inner := Array.take outer 0 in
            Array.consume Array.sum inner;
    """
        )
    )
    assert not errors, errors
    assert driver.run() == 7


def test_copy_instance_cannot_make_a_linear_handle_unrestricted():
    _, errors = compile_source("""
        open Copy;
        import Array;
        instance : Copy (Array Int) where
            duplicate x := x;
    """)
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_immutable_container_elements_are_copyable():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
        import Array;
        open Maybe;
        def main (_:Int):Int :=
            let 1 values := #[Maybe.just 7] in
            let value := Array.get values 0 in
            let again := Array.get values 0 in
            let _ := Array.dispose values in
            Maybe.withDefault 0 value + Maybe.withDefault 0 again;
    """
        )
    )
    assert not errors, errors
    assert driver.run() == 14


def test_statistics_can_observe_the_same_array_repeatedly():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    errors = list(
        driver.parse(
            aeon_code="""
        import Array;
        import Statistics;
        def main (_:Int):Float :=
            let 1 xs := #[1.0,2.0,3.0,4.0] in
            let below := Statistics.proportionBelow xs 3.0 in
            let above := Statistics.proportionAbove xs 2.0 in
            let between := Statistics.proportionBetween xs 1.0 4.0 in
            let total := Statistics.sum xs in
            let _ := Array.dispose xs in
            below + above + between + total;
    """
        )
    )
    assert not errors, errors
    assert driver.run() == 11.5
