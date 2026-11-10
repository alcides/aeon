"""Exercise all full TDSyn modes through the driver and the runtime list value."""

import pytest

from aeon.core.substitutions import substitution
from aeon.core.terms import Var
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.utils.name import Name


@pytest.mark.parametrize(
    "backend,length,first",
    [
        (backend, length, None)
        for backend in ("tdsyn_enumerative", "tdsyn_backward", "tdsyn_random")
        for length in (0, 1, 10)
    ]
    + [("tdsyn_enumerative", 12, 42)],
)
def test_synthesize_exact_list_length(backend, length, first):
    # The larger, doubly refined case takes nearly 20 seconds even in isolation.
    # This checks synthesis and runtime structure, not latency under CI contention.
    budget = 120 if first is not None else 20
    driver = AeonDriver(AeonConfig(backend, SilentSynthesisUI(), budget))
    refinement = f"List.size xs = {length}"
    if first is not None:
        refinement += f" && List.first xs = {first}"
    assert not list(driver.parse(aeon_code=f"open List\ndef result : {{xs:(List Int) | {refinement}}} := ?body;"))
    assert driver.has_synth()
    target = driver.incomplete_functions[0][0]
    driver.synth()
    driver.core = substitution(driver.core, Var(target), Name("main", 0))
    value = driver.run()
    elements = []
    while isinstance(value, tuple) and len(value) == 3 and value[0] == "List_cons":
        elements.append(value[1])
        value = value[2]
    assert value == ("List_nil",)
    assert len(elements) == length
    assert all(type(element) is int for element in elements)
    if first is not None:
        assert elements[0] == first
