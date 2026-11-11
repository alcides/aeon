"""Missing map entries have an explicit, type-correct result."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


@pytest.mark.parametrize("key,expected", [(1, 42), (2, 99)])
@pytest.mark.parametrize("lookup", ["Maybe.withDefault 99 (Map.get m KEY)", "Map.get_or m KEY 99"])
def test_map_lookup_present_and_absent(key, expected, lookup):
    source = """
    import Map;
    import Maybe;
    def main(u:Int):Int :=
        let m := Map.set Map.new 1 42 in
        LOOKUP;
    """.replace("LOOKUP", lookup.replace("KEY", str(key)))
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0))
    assert not driver.parse(aeon_code=source)
    assert driver.run() == expected


def test_map_missing_value_cannot_be_used_as_an_integer():
    driver = AeonDriver(AeonConfig("enumerative", SilentSynthesisUI(), 0))
    assert driver.parse(
        aeon_code="""
    import Map;
    def main(u:Int):Int := Map.get{Int}{Int} (Map.new{Int}{Int}) 0 + 1;
    """
    )
