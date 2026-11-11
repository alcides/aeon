"""Opt-in runtime refinement verification (issue #443)."""

from __future__ import annotations

import pytest

from aeon.backend.liquid_eval import UninterpretedInLiquid, eval_liquid_bool
from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
from aeon.core.types import t_int
from aeon.facade.api import ContractViolationError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


def _driver(source: str, *, contracts: bool = False) -> AeonDriver:
    cfg = AeonConfig(
        synthesizer="random_search",
        synthesis_ui=SilentSynthesisUI(),
        synthesis_budget=0,
        no_main=False,
        contracts=contracts,
    )
    driver = AeonDriver(cfg)
    errors = driver.parse(aeon_code=source)
    assert not errors, errors
    return driver


def test_native_violation_raises_with_runtime_verification():
    src = """
    def bad_abs (i:Int) : {v:Int | v >= 0} := native "i - 10"
    def main (a:Int) : Int := bad_abs 5 ;
    """
    driver = _driver(src, contracts=True)
    with pytest.raises(ContractViolationError) as exc:
        driver.run()
    assert exc.value.blame == "callee"
    assert "bad_abs" in exc.value.binding


def test_native_violation_silent_without_contracts():
    src = """
    def bad_abs (i:Int) : {v:Int | v >= 0} := native "i - 10"
    def main (a:Int) : Int := bad_abs 5 ;
    """
    driver = _driver(src, contracts=False)
    assert driver.run() == -5


def test_pure_aeon_refinement_checked():
    src = """
    def inc (i:Int) : {v:Int | v > i} := i + 1
    def main (a:Int) : Int := inc 3 ;
    """
    driver = _driver(src, contracts=True)
    assert driver.run() == 4


def test_caller_blame_on_bad_argument():
    from aeon.backend.contracts import ContractState, check_param_refinement
    from aeon.core.types import RefinedType, t_int
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar

    state = ContractState(uninterpreted={}, runtime={}, fn_types={})
    param = RefinedType(Name("x", 0), t_int, LiquidApp(Name(">=", 0), [LiquidVar(Name("x", 0)), LiquidLiteralInt(0)]))
    with pytest.raises(ContractViolationError) as exc:
        check_param_refinement(
            param,
            Name("i", 0),
            -1,
            state,
            callee=Name("use", 0),
            loc=None,
        )
    assert exc.value.blame == "caller"


def test_uninterpreted_predicate_is_skipped():
    src = """
    def p : (x:Int) -> Bool := uninterpreted
    def main (_:Int) : Int := 0 ;
    """
    driver = _driver(src, contracts=True)
    assert driver.run() == 0


def test_liquid_eval_uses_uninterpreted_dict():
    head = Name("fracBelow", 0)
    uninterpreted = {"fracBelow": t_int}
    pred = LiquidApp(head, [LiquidVar(Name("x", 0)), LiquidLiteralInt(1)])
    with pytest.raises(UninterpretedInLiquid):
        eval_liquid_bool(pred, {Name("x", 0): [1.0]}, uninterpreted=uninterpreted, runtime={})


@pytest.mark.parametrize("result", ["i - 10", "i + j - 1"])
def test_dependent_return_contract_remembers_all_arguments(result):
    source = f'''
    def bad(i:Int)(j:Int):{{v:Int | v > i + j}} := native "{result}";
    def main(u:Int):Int := bad 5 3;
    '''
    with pytest.raises(ContractViolationError) as exc:
        _driver(source, contracts=True).run()
    assert exc.value.blame == "callee"


def test_curried_contract_captures_each_partial_application_independently():
    from aeon.backend.contracts import ContractState, wrap_callable
    from aeon.core.parser import parse_type

    ty = parse_type("(x:Int) -> (y:{v:Int | v > x}) -> {r:Int | r > x}")
    fn = wrap_callable(lambda x: lambda y: y, ty, Name("f", 0), ContractState({}, {}, {}))
    low, high = fn(1), fn(10)
    assert low(5) == 5
    with pytest.raises(ContractViolationError) as exc:
        high(5)
    assert exc.value.blame == "caller"


def test_return_contract_can_read_lexical_environment():
    source = """
    def limit:Int := 10;
    def bad(i:Int):{v:Int | v > limit} := native "i";
    def main(u:Int):Int := bad 5;
    """
    with pytest.raises(ContractViolationError):
        _driver(source, contracts=True).run()
