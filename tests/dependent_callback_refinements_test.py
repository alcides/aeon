"""Callback result predicates retain the types of their dependent arguments."""

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

setup_logger()


@pytest.mark.parametrize("offset,valid", [(0, True), (1, False)])
def test_dependent_list_predicate_in_callback_result(offset, valid):
    source = f"""
import List
def accept (f:(bound:Int) -> (List Int){{|fun x => x >= bound|}}) : Unit := unit;
def candidate (limit:Int) : (List Int){{|fun x => x >= limit + {offset}|}} := ?h;
def probe : Unit := accept candidate;
"""
    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0, no_main=True))
    assert (not driver.parse(aeon_code=source)) == valid
