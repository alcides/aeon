"""Domain inference must preserve every source solution."""

from scripts.hakank_domains import infer_domains
from scripts.import_hakank_flatzinc import split_arguments


def infer(source):
    return infer_domains(source, split_arguments)


def test_auxiliary_sum_has_bounds_derived_from_operands():
    result = infer("""
        var -3..5: x;
        var 2..7: y;
        var int: sum;
        constraint int_lin_eq([1,1,-1],[x,y,sum],0);
    """)
    assert "var -1..12: sum" in result


def test_negative_coefficient_reverses_interval():
    result = infer("""
        var -3..5: x;
        var int: twice;
        constraint int_lin_eq([-2,-1],[x,twice],0);
    """)
    assert "var -10..6: twice" in result


def test_reified_relation_does_not_restrict_operand_domain():
    source = "var int: x; var bool: b; constraint int_eq_reif(x,4,b);"
    assert infer(source) == source


def test_unbounded_input_has_no_invented_cutoff():
    source = "var int: x; var int: y; constraint int_eq(x,y);"
    assert infer(source) == source


def test_two_sided_inequalities_derive_integer_bounds_inward():
    result = infer("""
        var int: x;
        constraint int_lin_le([2],[x],9);
        constraint int_lin_le([-2],[x],3);
    """)
    assert "var -1..4: x" in result
