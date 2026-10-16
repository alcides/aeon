"""The column-offset task uses the Dace DSL and preserves its examples."""

from pathlib import Path

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

setup_logger()


def test_col_offset_compiles_and_reference_satisfies_examples():
    path = Path(__file__).resolve().parents[1] / "examples/synthesis/dace/pbe/col_offset.ae"
    source = path.read_text()
    driver = AeonDriver(AeonConfig("random_search", SilentSynthesisUI(), 0, no_main=True))
    assert not driver.parse(aeon_code=source)
    assert driver.has_synth()
    assert len(next(v for v in driver.metadata.values() if v.get("examples"))["examples"]) == 3

    reference = "(if r = 0 then 0 else col_at col (r - 1))"
    assert not driver.parse(aeon_code=source.replace("?hole", reference))
    namespace = {}
    exec(driver.export("complete"), namespace)
    assert [namespace["complete"](r) for r in range(3)] == [0, 10, 20]
