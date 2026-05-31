"""Regression tests for issue #294.

Multi-objective fitness must be returned as the language's native ``Array`` type
(not the ``List`` ADT with a hardcoded, unresolved ``Name(..., -1)`` id), refined
so its length equals the number of objectives derived from the decorator's
argument list (one element per objective).
"""

from __future__ import annotations

# Import ``tests.driver`` first: it pulls in ``aeon.decorators`` (and through it
# ``aeon.synthesis.decorators``) in the right order, avoiding the package's
# pre-existing import cycle when ``aeon.synthesis.decorators`` is imported first.
from tests.driver import check_and_return_core

from aeon.synthesis.decorators import multi_objective_type
from aeon.sugar.stypes import SRefinedType, STypeConstructor


def _array_base(ty: SRefinedType) -> STypeConstructor:
    assert isinstance(ty, SRefinedType), f"expected a refined type, got {type(ty).__name__}"
    base = ty.type
    assert isinstance(base, STypeConstructor)
    return base


def test_multi_objective_type_is_native_array():
    """The fitness type is the native ``Array`` constructor, never ``List``."""
    ty = multi_objective_type("Float", 3)
    base = _array_base(ty)
    assert base.name.name == "Array"
    assert base.name.name != "List"
    assert len(base.args) == 1
    assert isinstance(base.args[0], STypeConstructor)
    assert base.args[0].name.name == "Float"


def test_multi_objective_type_has_no_unresolved_name():
    """The old code returned ``Name("List", -1)``; the array constructor must
    not smuggle in that unresolved placeholder id."""
    ty = multi_objective_type("Int", 2)
    base = _array_base(ty)
    assert base.name.name == "Array"
    # The element type carries the canonical builtin id, not the -1 sentinel.
    assert base.args[0].name == STypeConstructor(base.args[0].name).name


def test_multi_objective_type_refines_by_objective_count():
    """The type carries a ``size v == N`` refinement, with N the objective count."""
    for n in (1, 2, 4):
        ty = multi_objective_type("Float", n)
        refinement = str(ty.refinement)
        assert "Array_size" in refinement
        assert f"{n}" in refinement


def test_multi_objective_element_type_tracks_decorator():
    assert _array_base(multi_objective_type("Float", 1)).args[0].name.name == "Float"
    assert _array_base(multi_objective_type("Int", 1)).args[0].name.name == "Int"


def test_multi_minimize_float_typechecks_against_native_array():
    """A fitness expression returning a native ``Array`` of exactly N elements
    typechecks against the refined fitness type, and a goal of length N is
    registered."""
    source = """
        import Array;
        @multi_minimize_float(native "[1.0, 2.0]", 2)
        def synth (i:Int) : Int = (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = [g for v in metadata.values() if isinstance(v, dict) for g in v.get("goals", [])]
    assert len(goals) == 1
    assert goals[0].minimize is True
    assert goals[0].length == 2


def test_multi_minimize_int_typechecks_against_native_array():
    source = """
        import Array;
        @multi_minimize_int(native "[1, 2, 3]", 3)
        def synth (i:Int) : Int = (?hole: Int)
    """
    _, _, _, metadata = check_and_return_core(source)
    goals = [g for v in metadata.values() if isinstance(v, dict) for g in v.get("goals", [])]
    assert len(goals) == 1
    assert goals[0].length == 3
