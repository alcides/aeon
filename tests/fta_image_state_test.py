import pytest

from aeon.core.terms import Var
from aeon.synthesis.modules.fta.synthesizer import _value_state
from aeon.utils.name import Name

Image = pytest.importorskip("PIL.Image")


def test_equal_images_have_equal_hashable_states():
    image = Image.new("RGB", (2, 2), "red")
    state = _value_state(image, Var(Name("first", 1)))
    assert state == _value_state(image.copy(), Var(Name("second", 2)))
    hash(state)


def test_image_state_is_snapshot_and_preserves_metadata():
    image = Image.new("RGB", (2, 2), "red")
    term = Var(Name("image", 1))
    before = _value_state(image, term)
    image.putpixel((0, 0), (0, 0, 0))
    after = _value_state(image, term)
    assert before != after
    image.info["description"] = "different"
    assert after != _value_state(image, term)


def test_palettes_distinguish_image_states():
    first = Image.new("P", (1, 1))
    second = first.copy()
    first.putpalette([255, 0, 0] * 256)
    second.putpalette([0, 255, 0] * 256)
    assert _value_state(first, Var(Name("a", 1))) != _value_state(second, Var(Name("b", 2)))


def test_unknown_unhashable_values_are_not_merged_by_repr():
    class Opaque:
        __hash__ = None

        def __repr__(self):
            return "opaque"

    first, second = Var(Name("a", 1)), Var(Name("b", 2))
    states = [_value_state(Opaque(), term) for term in (first, second)]
    assert states[0] != states[1]
    assert all(isinstance(hash(state), int) for state in states)


def test_fta_stops_observing_atoms_after_first_solution():
    from aeon.core.types import t_int
    from aeon.synthesis.modules.fta.synthesizer import FTASynthesizer
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.typechecking.context import TypingContext

    first, second = Name("first", 1), Name("second", 2)
    calls = []

    def output(term):
        calls.append(term)
        return 7

    FTASynthesizer().synthesize(
        TypingContext().with_var(first, t_int).with_var(second, t_int),
        t_int,
        lambda term: True,
        lambda term: [],
        Name("f", 3),
        {},
        budget=1,
        ui=SilentSynthesisUI(),
        output_value=output,
    )
    assert len(calls) == 1
