"""Value bindings enforce supported refinements only when opted in."""

import pytest

from aeon.errors import ContractViolationError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


@pytest.mark.parametrize("contracts", [False, True])
@pytest.mark.parametrize(
    "body",
    [
        'def bad:{v:Int | v > 0} := native "-1"; def main(_ :Int):Int := bad;',
        'def main(_ :Int):Int := let bad:{v:Int | v > 0} := native "-1" in bad;',
        'def limit:Int := 5; def bad:{v:Int | v > limit} := native "4"; def main(_ :Int):Int := bad;',
        'mutual def bad:{v:Int | v > 0} := native "-1"; end def main(_ :Int):Int := bad;',
    ],
)
def test_bad_native_value_is_checked_at_its_binding(contracts, body):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, contracts=contracts))
    assert not driver.parse(aeon_code=body)
    if contracts:
        with pytest.raises(ContractViolationError) as error:
            driver.run()
        assert error.value.blame == "callee"
        assert error.value.binding == "bad"
    else:
        assert driver.run() in (-1, 4)


def test_valid_native_constant_and_pure_value_keep_their_values():
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, contracts=True))
    assert not driver.parse(
        aeon_code="""
        def limit:Int := 5;
        def good:{v:Int | v > limit} := native "6";
        def main(_ :Int):Int := good;
    """
    )
    assert driver.run() == 6
