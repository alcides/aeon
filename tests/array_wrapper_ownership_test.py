"""Read wrappers must not manufacture aliases to a linear buffer."""

from pathlib import Path

import pytest

from aeon.errors import LinearityError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def parse(source):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    return driver, list(driver.parse(aeon_code="import Array;\n" + source))


@pytest.mark.parametrize(
    "make,project",
    [
        ("Array.get_at #[1,2] 0", "Array.got_array"),
        ("Array.copy #[1,2]", "Array.fst_array"),
        ("Array.copy #[1,2]", "Array.snd_array"),
    ],
)
def test_projecting_a_buffer_twice_is_rejected(make, project):
    _, errors = parse(f"""
        def main(_ :Int):Int :=
            let 1 token := {make} in
            let 1 a := {project} token in
            let 1 b := {project} token in
            (Array.consume Array.sum) a + (Array.consume Array.sum) b;
    """)
    assert any(isinstance(error, LinearityError) for error in errors), errors


def test_mutating_one_alias_cannot_invalidate_another_length_proof():
    _, errors = parse("""
        def push (1 a:(Array Int)) (x:Int):
            {b:(Array Int) | Array.size b = Array.size a + 1} := native "a.append(x) or a";
        def main(_ :Int):{n:Int | n = 2} :=
            let 1 p := Array.get_at #[1,2] 0 in
            let 1 a := Array.got_array p in
            let 1 b := Array.got_array p in
            let 1 changed := push a 3 in
            let ignored := Array.dispose changed in
            let n := Array.length b in
            let ignored := Array.dispose b in
            n;
    """)
    assert any(isinstance(error, LinearityError) for error in errors), errors


@pytest.mark.parametrize(
    "body,expected",
    [
        ("Array.with_get (Array.get_at #[1,2] 0) (fun x => fun a => x + (Array.consume Array.sum) a)", 4),
        (
            "Array.with_pair (Array.copy #[1,2]) (fun a => fun b => (Array.consume Array.sum) a + (Array.consume Array.sum) b)",
            6,
        ),
    ],
)
def test_continuations_recover_both_fields_once(body, expected):
    driver, errors = parse(f"def main(_ :Int):Int := {body};")
    assert not errors, errors
    assert driver.run() == expected


def test_length_after_update_preserves_exact_size():
    driver, errors = parse("""
        def main(_ :Int):{n:Int | n = 2} :=
            let 1 arr := #[5,9] in
            let before := Array.length arr in
            let 1 updated := Array.set arr 0 7 in
            let after := Array.length updated in
            let ignored := Array.dispose updated in
            after;
    """)
    assert not errors, errors
    assert driver.run() == 2


def test_copy_continuation_exposes_independent_buffers():
    driver, errors = parse("""
        def push (1 a:(Array Int)) (x:Int):
            {b:(Array Int) | Array.size b = Array.size a + 1} := native "a.append(x) or a";
        def main(_ :Int):Int :=
            Array.with_pair (Array.copy #[1,2]) (fun a => fun b =>
                let 1 changed := push a 3 in
                let ignored := Array.dispose changed in
                let n := Array.length b in
                let ignored := Array.dispose b in
                n);
    """)
    assert not errors, errors
    assert driver.run() == 2


def test_continuation_keeps_element_refinements_and_index_bounds():
    driver, errors = parse("""
        def positive (1 x:{v:Int | v > 0}):Int := x;
        def main(_ :Int):Int :=
            Array.with_get (Array.get_at #[1,2] 0) (fun value => fun arr =>
                positive value + positive (Array.take arr 1));
    """)
    assert not errors, errors
    assert driver.run() == 3


@pytest.mark.parametrize(
    "path",
    [
        "examples/testing/array_tests.ae",
        "examples/testing/string_tests.ae",
        "examples/ffi/array_linear.ae",
        "examples/pbt/pbt_reverse.ae",
    ],
)
def test_wrapper_examples_use_the_linear_api(path):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not driver.parse(aeon_code=Path(path).read_text(), filename=path)
