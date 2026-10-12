"""Check interchange semantics rather than just generated text."""

import pytest

from scripts.import_hakank_flatzinc import Translator, Unsupported
from tests.ortools_cpsat_test import _parse, _solve, _values


def solve(source):
    model = Translator("fixture", source).translate()
    result = _solve(_parse(model.render({"source_url": "https://example.org/fixture"})))
    assert all(value is not None for value in result.values())
    return model, _values(result)


@pytest.mark.parametrize(
    "numerator,denominator,quotient,remainder", [(-7, 3, -2, -1), (7, -3, -2, 1), (-7, -3, 2, -1), (7, 3, 2, 1)]
)
def test_signed_division_and_remainder(numerator, denominator, quotient, remainder):
    model, values = solve(f"""
        var -10..10: q;
        var -10..10: r;
        constraint int_div({numerator},{denominator},q);
        constraint int_mod({numerator},{denominator},r);
        solve satisfy;
    """)
    assert values["h_decision0"] == quotient
    assert values["h_decision1"] == remainder


def test_sets_have_symbolic_membership_and_cardinality():
    model, values = solve("""
        var set of {2,5,9}: chosen;
        var 0..3: count;
        constraint set_in(5,chosen);
        constraint set_card(chosen,count);
        solve minimize count;
    """)
    members = model.data["set_identifiers"]["chosen"]
    assert {int(item) for item, name in members.items() if values["h_" + name]} == {5}
    assert values["h_decision3"] == 1


def test_set_operations_preserve_absent_universe_members():
    model, values = solve("""
        var set of 1..3: result;
        constraint set_union({1},{3},result);
        constraint set_ne(result,{1});
        solve satisfy;
    """)
    members = model.data["set_identifiers"]["result"]
    assert {int(item) for item, name in members.items() if values["h_" + name]} == {1, 3}


def test_dynamic_element_is_one_based():
    model, values = solve("""
        var 1..3: index;
        var 0..30: value;
        array [1..3] of int: choices = [10,20,30];
        constraint array_int_element(index,choices,value);
        constraint int_eq(value,20);
        solve satisfy;
    """)
    assert values["h_decision0"] == 2
    assert values["h_decision1"] == 20


def test_reification_is_equivalence():
    model, values = solve("""
        var 0..4: number;
        var bool: equal;
        constraint int_eq_reif(number,2,equal);
        constraint bool_eq(equal,true);
        solve satisfy;
    """)
    assert values == {"h_decision0": 2, "h_decision1": True}


def test_unsupported_operation_is_not_omitted():
    with pytest.raises(Unsupported, match="constraint unknown"):
        Translator("unsupported", "var 0..1: x; constraint unknown(x); solve satisfy;").translate()


def test_float_constants_and_integer_conversion():
    model, values = solve("""
        var 0..2: integer;
        var 0.0..2.0: real;
        var 0.0..0.002: small;
        constraint int2float(integer,real);
        constraint float_eq(real,2.0);
        constraint float_times(small,0.0005,0.000001);
        solve minimize small;
    """)
    assert values == {"h_decision0": 2, "h_decision1": 2.0, "h_decision2": 0.002}


@pytest.mark.parametrize(
    "left,right",
    [([], []), ([], [1]), ([1], []), ([1], [1, 2]), ([1, 2], [1]), ([1, 3], [2]), ([2], [1, 3]), ([1, 3], [1, 2])],
)
def test_set_order_compares_sorted_elements(left, right):
    def literal(items):
        return "{" + ",".join(map(str, items)) + "}"

    model, values = solve(f"""
        var bool: ordered;
        constraint set_le_reif({literal(left)},{literal(right)},ordered);
        solve satisfy;
    """)
    assert values["h_decision0"] == (left <= right)


def test_vector_linear_expression_preserves_coefficients():
    model, values = solve("""
        var 0..10: x;
        constraint int_lin_eq([1,-2,3,-4],[x,x,x,x],-12);
        solve satisfy;
    """)
    assert "Vec.dot" in model.render({"source_url": "https://example.org/linear"})
    assert values["h_decision0"] == 6


def test_compact_render_keeps_holes_and_bool_decisions():
    model = Translator(
        "packing",
        """
        var 0..3: x;
        var bool: chosen;
        constraint bool_eq(chosen,true);
        constraint int_eq(x,3);
        solve satisfy;
    """,
    ).translate()
    model.compact = True
    source = model.render({"source_url": "https://example.org/packing"})
    assert "DecisionTree.leaf (?h_decision0" in source
    assert "def decision0" not in source
    assert _values(_solve(_parse(source))) == {"h_decision0": 3, "h_decision1": True}
