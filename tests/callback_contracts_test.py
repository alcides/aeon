"""Higher-order contracts guard callbacks and preserve boundary blame."""

import pytest

from aeon.backend.contracts import ContractState, wrap_callable
from aeon.core.parser import parse_type
from aeon.errors import ContractViolationError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


@pytest.mark.parametrize("contracts", [False, True])
@pytest.mark.parametrize(
    "source,blame",
    [
        (
            """def use(f:(x:{v:Int | v > 0})->Int):Int := native "f(-1)";
        def main(_ :Int):Int := use (fun x => x);""",
            "callee",
        ),
        (
            """def use(f:(x:Int)->{v:Int | v > 0}):Int := f 1;
        def main(_ :Int):Int := use (fun x => native "-1");""",
            "caller",
        ),
    ],
)
def test_inline_callback_is_checked_only_when_enabled(contracts, source, blame):
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, contracts=contracts))
    assert not driver.parse(aeon_code=source)
    if contracts:
        with pytest.raises(ContractViolationError) as error:
            driver.run()
        assert error.value.blame == blame
        assert error.value.binding == "use"
    else:
        assert driver.run() == -1


def test_callback_contract_captures_each_outer_partial_application():
    ty = parse_type("(n:Int) -> (f:((x:{v:Int | v > n}) -> Int)) -> Int")
    use = wrap_callable(lambda n: lambda f: f(5), ty, Name("use", 0), ContractState({}, {}, {}))
    low, high = use(0), use(10)
    assert low(lambda x: x) == 5
    with pytest.raises(ContractViolationError) as error:
        high(lambda x: x)
    assert error.value.blame == "callee"


def test_curried_callback_preserves_dependent_return_and_blame():
    ty = parse_type("(f:((x:Int) -> (y:Int) -> {v:Int | v > x + y})) -> Int")
    use = wrap_callable(lambda f: f(2)(3), ty, Name("use", 0), ContractState({}, {}, {}))
    assert use(lambda x: lambda y: x + y + 1) == 6
    with pytest.raises(ContractViolationError) as error:
        use(lambda x: lambda y: x + y)
    assert error.value.blame == "caller"


def test_callback_accepting_another_callback_flips_blame_again():
    ty = parse_type("(f:((g:((x:{v:Int | v > 0}) -> Int)) -> Int)) -> Int")
    use = wrap_callable(lambda f: f(lambda x: x), ty, Name("use", 0), ContractState({}, {}, {}))
    assert use(lambda g: g(1)) == 1
    with pytest.raises(ContractViolationError) as error:
        use(lambda g: g(-1))
    assert error.value.blame == "caller"
