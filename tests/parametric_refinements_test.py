from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile

# ---------------------------------------------------------------------------
# id – explicit + implicit refinement application, mismatches, bool, equality
# ---------------------------------------------------------------------------

ID_DEF = "def id : forall t : B, forall <p : t -> Bool>, (x : t<p>) -> t<p> = Λ t : B => \\x -> x;"


def test_id_explicit_and_implicit_int_predicate():
    """Explicit {\\n -> ...} and inferred predicate both propagate on Int."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id[Int]{{\\n -> n > 0}} x;
    z : Int | z > 0 = id[Int] y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_id_rejects_mismatched_predicate():
    """Output refinement must follow the argument; implicit application."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y < 0 = id[Int] x;
    print (y)
}}
"""
    assert not check_compile(source, st_top)


def test_id_preserves_equality_predicate():
    """Exact-value predicate is preserved (distinct from order-only predicates)."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x == 42 = 42;
    y : Int | y == 42 = id[Int]{{\\n -> n == 42}} x;
    print (y)
}}
"""
    assert check_compile(source, st_top)


def test_id_bool_predicates():
    """Bool: satisfied refinement passes; impossible refinement fails."""
    ok = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    b : Bool | b == true = true;
    r : Bool | r == true = id[Bool] b;
    print (r)
}}
"""
    bad = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    b : Bool | b == false = false;
    r : Bool | r == true = id[Bool] b;
    print (r)
}}
"""
    assert check_compile(ok, st_top)
    assert not check_compile(bad, st_top)


# ---------------------------------------------------------------------------
# const
# ---------------------------------------------------------------------------

CONST_DEF = (
    "def const : forall t : B, forall <p : t -> Bool>,"
    " (x : t | p x) -> (y : t) -> {v : t | p v} = Λ t : B => \\x -> \\y -> x;"
)


def test_const_propagates_first_argument_predicate():
    source = f"""
{CONST_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 5;
    r : Int | r > 0 = const[Int] x 99;
    print (r)
}}
"""
    assert check_compile(source, st_top)


def test_const_rejects_wrong_predicate_on_result():
    source = f"""
{CONST_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 5;
    r : Int | r < 0 = const[Int] x 99;
    print (r)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# Chained id and predicate strengthening
# ---------------------------------------------------------------------------


def test_id_chained_implicit():
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 7;
    y : Int | y > 0 = id[Int] x;
    z : Int | z > 0 = id[Int] y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_id_chained_rejects_stricter_predicate():
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 7;
    y : Int | y > 0 = id[Int] x;
    z : Int | z > 10 = id[Int] y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# User wrapper around id
# ---------------------------------------------------------------------------

WRAP_DEF = (
    "def wrap : forall t : B, forall <p : t -> Bool>, (x : t<p>) -> t<p> = Λ t : B => \\x -> id[t]{\\v -> v == x} x;"
)


def test_wrapper_around_id():
    source_ok = f"""
{ID_DEF}
{WRAP_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 4;
    b : Int | b > 0 = wrap[Int] a;
    print (b)
}}
"""
    source_bad = f"""
{ID_DEF}
{WRAP_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b > 10 = wrap[Int] a;
    print (b)
}}
"""
    assert check_compile(source_ok, st_top)
    assert not check_compile(source_bad, st_top)


# ---------------------------------------------------------------------------
# Multiple independent predicates in one program
# ---------------------------------------------------------------------------


def test_two_independent_predicates():
    source_ok = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b < 0 = 0 - 1;
    ra : Int | ra > 0 = id[Int] a;
    rb : Int | rb < 0 = id[Int] b;
    print (ra)
}}
"""
    source_bad = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b < 0 = 1;
    ra : Int | ra > 0 = id[Int] a;
    rb : Int | rb > 0 = id[Int] b;
    print (ra)
}}
"""
    assert check_compile(source_ok, st_top)
    assert not check_compile(source_bad, st_top)


# ---------------------------------------------------------------------------
# maxI – Int-only refinement polymorphism, max preserves predicate p
# ---------------------------------------------------------------------------

MAXI_DEF = (
    "def maxI : forall <p : Int -> Bool>, "
    "(x : Int<p>) -> (y : Int<p>) -> Int<p> = "
    "\\x -> \\y -> if x < y then y else x;"
)


def test_maxI_implicit_predicate():
    """Inferred p; result must satisfy the same refinement as arguments."""
    source = f"""
{MAXI_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z > 0 = maxI x y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_maxI_inferred_predicate_wider_than_args():
    """
    Inferred p where the result's refinement is wider than each argument.
    """
    source = f"""
{MAXI_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 1 = 5;
    z : Int | z > (-1) = maxI x y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_maxI_explicit_predicate():
    """Explicit refinement application on maxI."""
    source = f"""
{MAXI_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z > 0 = maxI{{\\n -> n > 0}} x y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_maxI_rejects_stricter_result_predicate():
    """Annotated result stricter than what max of the given literals establishes."""
    source = f"""
{MAXI_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z > 10 = maxI x y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


def test_maxI_rejects_wrong_predicate_on_result():
    """Max of positives is non-negative; cannot assign a strictly negative refinement."""
    source = f"""
{MAXI_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = 5;
    z : Int | z < 0 = maxI x y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# $ – Haskell-style function application, refinement-preserving
# ---------------------------------------------------------------------------


def test_dollar_preserves_output_refinement():
    source = """
def inc : (x:Int) -> {y:Int | y > 0} = \\x -> if x > 0 then x + 1 else 1;

def main (args:Int) : Unit {
    r : Int | r > 0 = inc $ 5;
    print (r)
}
"""
    assert check_compile(source, st_top)


def test_dollar_right_associative_chain():
    source = """
def inc : (x:Int) -> {y:Int | y > 0} = \\x -> if x > 0 then x + 1 else 1;
def dbl : (x:Int) -> {y:Int | y > 0} = \\x -> if x > 0 then x + x else 1;

def main (args:Int) : Unit {
    r : Int | r > 0 = inc $ dbl $ 3;
    print (r)
}
"""
    assert check_compile(source, st_top)


def test_dollar_rejects_stricter_refinement():
    source = """
def inc : (x:Int) -> {y:Int | y > 0} = \\x -> if x > 0 then x + 1 else 1;

def main (args:Int) : Unit {
    r : Int | r > 100 = inc $ 5;
    print (r)
}
"""
    assert not check_compile(source, st_top)


def test_dollar_lower_precedence_than_plus():
    source = """
def inc : (x:Int) -> {y:Int | y > 0} = \\x -> if x > 0 then x + 1 else 1;

def main (args:Int) : Unit {
    r : Int | r > 0 = inc $ 2 + 3;
    print (r)
}
"""
    assert check_compile(source, st_top)
