"""Higher-order benchmark types must unify modulo bound argument names."""

import pytest

from aeon.core.multiplicity import M1, MOmega
from aeon.elaboration import _resolve_uvars, unify_single
from aeon.errors import UnificationFailedError
from aeon.sugar.ast_helpers import st_int
from aeon.sugar.program import SVar
from aeon.sugar.stypes import SAbstractionType, SRefinedType
from aeon.utils.name import Name


def test_independent_function_binders_unify():
    first = SAbstractionType(Name("x", 101), st_int, st_int)
    second = SAbstractionType(Name("y", 102), st_int, st_int)
    assert unify_single("benchmark", [first, second]) == first


def test_dependent_results_follow_bound_names_but_not_free_names():
    x, y, v = Name("x", 101), Name("y", 102), Name("v", 103)
    first = SAbstractionType(x, st_int, SRefinedType(v, st_int, SVar(x)))
    second = SAbstractionType(y, st_int, SRefinedType(v, st_int, SVar(y)))
    assert unify_single("benchmark", [first, second]) == first
    free = SAbstractionType(y, st_int, SRefinedType(v, st_int, SVar(x)))
    with pytest.raises(UnificationFailedError):
        unify_single("benchmark", [first, free])


@pytest.mark.parametrize("multiplicity,instance", [(M1, False), (MOmega, True)])
def test_resolution_preserves_function_attributes(multiplicity, instance):
    typ = SAbstractionType(Name("x", 101), st_int, st_int, multiplicity=multiplicity, is_instance=instance)
    assert _resolve_uvars(typ) == typ
    with pytest.raises(UnificationFailedError):
        unify_single("benchmark", [typ, SAbstractionType(Name("y", 102), st_int, st_int)])
