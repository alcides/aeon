from __future__ import annotations

import pytest

from aeon.core.equality import canonicalize_type, core_type_equality
from aeon.core.liquid import LiquidApp, LiquidVar
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    Top,
    Type,
    TypeConstructor,
    TypeVar,
    t_bool,
    t_int,
)
from aeon.synthesis.grammar.grammar_generation import _get, extract_all_types
from aeon.utils.name import Name


def _eq(av: Name, rv: Name) -> Type:
    """Builds `(av:Int) -> {rv:Int | rv == av}` for the given binder names."""
    ref = LiquidApp(Name("==", 0), [LiquidVar(rv), LiquidVar(av)])
    return AbstractionType(av, t_int, RefinedType(rv, t_int, ref))


def _refined(name: Name) -> RefinedType:
    """Builds `{name:Int | name == name}` for the given bound name."""
    ref = LiquidApp(Name("==", 0), [LiquidVar(name), LiquidVar(name)])
    return RefinedType(name, t_int, ref)


def test_refined_alpha_collapse():
    """Alpha-variant refined types map to a single grammar class."""
    t1 = _refined(Name("a", 1))
    t2 = _refined(Name("b", 2))
    assert canonicalize_type(t1) == canonicalize_type(t2)

    type_info = extract_all_types([t1, t2])
    # Both variants resolve to the same (single) class object.
    assert _get(type_info, t1) is _get(type_info, t2)
    # Only one refined abstract class is produced.
    refined_classes = [k for k in type_info if isinstance(k, RefinedType)]
    assert len(refined_classes) == 1


def test_abstraction_alpha_collapse():
    """Alpha-variant abstraction types map to a single grammar class."""
    t1 = _eq(Name("a", 1), Name("r", 3))
    t2 = _eq(Name("b", 2), Name("s", 4))
    assert canonicalize_type(t1) == canonicalize_type(t2)

    type_info = extract_all_types([t1, t2])
    assert _get(type_info, t1) is _get(type_info, t2)
    abstraction_classes = [k for k in type_info if isinstance(k, AbstractionType)]
    assert len(abstraction_classes) == 1


def test_nested_abstraction_distinct_binders():
    """Refinements referencing different nested binders stay distinct."""
    x, y, r = Name("x", 1), Name("y", 2), Name("r", 3)

    def nested(referenced: Name) -> AbstractionType:
        ref = LiquidApp(Name("==", 0), [LiquidVar(r), LiquidVar(referenced)])
        inner = AbstractionType(y, t_int, RefinedType(r, t_int, ref))
        return AbstractionType(x, t_int, inner)

    n1 = nested(x)
    n2 = nested(y)
    assert not core_type_equality(n1, n2)
    assert canonicalize_type(n1) != canonicalize_type(n2)

    type_info = extract_all_types([n1, n2])
    assert _get(type_info, n1) is not _get(type_info, n2)


# Oracle: canonical-form equality must agree with the trusted alpha-equality.
_oracle_types = [
    t_int,
    t_bool,
    TypeConstructor(Name("List", 0), [t_int]),
    TypeVar(Name("T", 0)),
    Top(),
    _refined(Name("a", 1)),
    _refined(Name("b", 2)),
    _eq(Name("a", 1), Name("r", 3)),
    _eq(Name("b", 2), Name("s", 4)),
    AbstractionType(Name("x", 1), t_int, t_bool),
    AbstractionType(Name("z", 9), t_int, t_bool),
    AbstractionType(Name("x", 1), t_bool, t_int),
]


@pytest.mark.parametrize("t1", _oracle_types)
@pytest.mark.parametrize("t2", _oracle_types)
def test_canonicalize_matches_core_type_equality(t1, t2):
    canon_eq = canonicalize_type(t1) == canonicalize_type(t2)
    alpha_eq = core_type_equality(t1, t2)
    assert canon_eq == alpha_eq


def test_top_shared():
    """Top() always resolves to the single shared ae_top root."""
    from aeon.synthesis.grammar.grammar_generation import ae_top

    type_info = extract_all_types([t_int, Top()])
    assert _get(type_info, Top()) is ae_top
    # canonical key for Top stored exactly once
    top_keys = [k for k in type_info if isinstance(k, Top)]
    assert len(top_keys) == 1


def test_var_lookup_via_alpha_variant():
    """A var typed with one alpha-variant resolves against a class built from another."""
    from aeon.synthesis.grammar.grammar_generation import create_var_nodes

    built = _eq(Name("a", 1), Name("r", 3))
    lookup = _eq(Name("b", 2), Name("s", 4))

    type_info = extract_all_types([built])
    # The lookup variant is not a structural key, but resolves via canonicalization.
    assert lookup not in type_info
    assert _get(type_info, lookup) is _get(type_info, built)

    # create_var_nodes must find the alpha-variant typed variable.
    nodes = create_var_nodes([(Name("f", 7), lookup)], type_info)
    assert nodes, "expected at least one var node for the alpha-variant typed variable"
