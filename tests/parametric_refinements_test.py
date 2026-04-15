from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile

ID_IMPLICIT_TYPE_IMPLICIT_REF = "def id : (x : t<p>) -> t<p> = \\x -> x;"


def test_parametric_explicit_type_implicit_refinement_compiles():
    source = """
def id : forall t : B, (x : t<p>) -> t<p> = Λ t : B => Λ < p : t -> Bool > => \\x -> x;
def main (args:Int) : Unit {
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id[Int] x;
    print (y)
}
"""
    assert check_compile(source, st_top)


def test_parametric_explicit_type_explicit_refinement_compiles():
    source = """
def id : forall t : B, forall <p : t -> Bool>, (x : t<p>) -> t<p> = Λ t : B => Λ < p : t -> Bool > => \\x -> x;
def main (args:Int) : Unit {
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id[Int]{\\n -> n > 0} x;
    print (y)
}
"""
    assert check_compile(source, st_top)


def test_parametric_implicit_type_implicit_refinement_compiles():
    source = f"""
{ID_IMPLICIT_TYPE_IMPLICIT_REF}
def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id x;
    print (y)
}}
"""
    assert check_compile(source, st_top)


def test_parametric_rejects_mismatched_predicate():
    source = f"""
{ID_IMPLICIT_TYPE_IMPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y < 0 = id x;
    print (y)
}}
"""
    assert not check_compile(source, st_top)


def test_parametric_rejects_stricter_result_after_chained_id():
    """Chained id cannot justify a strictly stronger predicate."""
    source = f"""
{ID_IMPLICIT_TYPE_IMPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 7;
    y : Int | y > 0 = id x;
    z : Int | z > 10 = id y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


MAXI_EXPLICIT_REF = (
    "def maxI : forall <p : Int -> Bool>, (x : Int<p>) -> (y : Int<p>) -> Int<p> = "
    "Λ < p : Int -> Bool > => \\x -> \\y -> if x < y then y else x;"
)

MAXI_IMPLICIT_REF = "def maxI : (x : Int<p>) -> (y : Int<p>) -> Int<p> = \\x -> \\y -> if x < y then y else x;"


def test_maxI_explicit_forall_p_compiles():
    """forall <p> on Int only; no type polymorphism; Λ < p => in term."""
    source = f"""
{MAXI_EXPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z > 0 = maxI x y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_maxI_implicit_refinement_inferred_p():
    source = f"""
{MAXI_IMPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z > 0 = maxI x y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_maxI_rejects_stricter_result_predicate():
    source = f"""
{MAXI_IMPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z > 10 = maxI x y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


CONST_DEF = "def const : (x : t | p x) -> (y : t) -> {v : t | p v} = \\x -> \\y -> x;"


def test_const_propagates_first_argument_predicate():
    source = f"""
{CONST_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 5;
    r : Int | r > 0 = const x 99;
    print (r)
}}
"""
    assert check_compile(source, st_top)


def test_const_rejects_wrong_predicate_on_result():
    source = f"""
{CONST_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 5;
    r : Int | r < 0 = const x 99;
    print (r)
}}
"""
    assert not check_compile(source, st_top)


WRAP_DEF = "def wrap : (x : t<p>) -> t<p> = \\x -> id[t]{\\v -> v == x} x;"


def test_wrapper_around_explicit_type_id():
    source_ok = f"""
{ID_IMPLICIT_TYPE_IMPLICIT_REF}
{WRAP_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 4;
    b : Int | b > 0 = wrap a;
    print (b)
}}
"""
    source_bad = f"""
{ID_IMPLICIT_TYPE_IMPLICIT_REF}
{WRAP_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b > 10 = wrap a;
    print (b)
}}
"""
    assert check_compile(source_ok, st_top)
    assert not check_compile(source_bad, st_top)
