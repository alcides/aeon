"""GP constructs array expressions from its genome."""

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.synthesis.uis.api import SilentSynthesisUI


def test_gp_decodes_array_structure_with_refined_length():
    from aeon.core.substitutions import substitution
    from aeon.core.types import top
    from aeon.synthesis.identification import get_holes_info
    from aeon.synthesis.modules.genetic_programming import map_genome
    from aeon.synthesis.modules.native_search import expansions_for_hole, initial_partial, make_skip

    driver = AeonDriver(AeonConfig("none", SilentSynthesisUI(), 0))
    assert not driver.parse(
        aeon_code="""
        import Array;
        def selection (_:Unit): {a:(Array Bool) | Array.size a = 50} := ?solution;
        def main (_:Int):(Array Bool) := selection unit;
    """
    )
    assert driver.has_synth()
    with driver.session.activate():
        info = get_holes_info(driver.typing_ctx, driver.core, top, driver.incomplete_functions, refined_types=True)
        hole, (target, context) = next(iter(info.items()))
        initial = initial_partial(context, target)
        skip = make_skip(driver.incomplete_functions[0][0], driver.metadata)
        options = expansions_for_hole(initial, initial.holes[0], skip, prune=False)
        # Select a constructor production, not a preallocated array of holes.
        repeat = next(i for i, option in enumerate(options) if "Array_mk_repeat" in str(option.term))
        term = map_genome([repeat, 0], initial, skip)
        assert term is not None
        driver.core = substitution(driver.core, term, hole)
    result = driver.run()
    assert len(result) == 50
    assert all(type(item) is bool for item in result)
