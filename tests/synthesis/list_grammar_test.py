"""Regression test: opening the polymorphic ``List`` library and leaving a hole
must not crash synthesis hole-identification.

``List.map`` (and friends) elaborate to terms that mention ``cons``/``map``
carrying abstract refinements (``?rho_pred`` / ``?k``). ``get_holes_info`` used
to walk *every* top-level definition — including these hole-free library
bodies — and re-type each subterm, aborting with ``assert False`` on a shape it
did not model. Hole identification only needs to descend into subterms that
actually contain a hole, so hole-free library code is now skipped.
"""

from aeon.core.types import top
from aeon.synthesis.identification import get_holes_info
from tests.driver import check_and_return_core


def test_open_list_hole_does_not_crash_grammar_identification():
    code = """open List

def reverse (xs: (List Int)) : {l:(List Int) | List.size l == List.size xs} = ?hole;
"""
    term, ctx, _ectx, _metadata = check_and_return_core(code)

    # Previously raised AssertionError("Synthesis cannot infer the type ...").
    holes = get_holes_info(ctx, term, top, [], refined_types=True)

    assert any(name.name == "hole" for name in holes), holes
