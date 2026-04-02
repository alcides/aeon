from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile

# ---------------------------------------------------------------------------
# Parametric matrix: type quantifier (implicit vs explicit forall t) ×
# refinement quantifier (implicit t<p> only vs explicit forall <p : …>).
# ---------------------------------------------------------------------------

# Explicit forall t in type; refinement only via t<p> (no forall <p> in type).
ID_EXPLICIT_TYPE_IMPLICIT_REF = (
    "def id : forall t : B, (x : t<p>) -> t<p> = Λ t : B => Λ < p : t -> Bool > => \\x -> x;"
)

# Both quantifiers written in the type; term must bind both.
ID_EXPLICIT_TYPE_EXPLICIT_REF = (
    "def id : forall t : B, forall <p : t -> Bool>, (x : t<p>) -> t<p> = Λ t : B => Λ < p : t -> Bool > => \\x -> x;"
)

# Free type variable t + t<p>; desugar adds Λ t / Λ p around body (no Λ in source).
ID_IMPLICIT_TYPE_IMPLICIT_REF = "def id : (x : t<p>) -> t<p> = \\x -> x;"


def _main_id_int_implicit_app() -> str:
    """id[Int] with inferred predicate from argument refinement."""
    return """
def main (args:Int) : Unit {
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id[Int] x;
    print (y)
}
"""


def _main_id_int_explicit_app() -> str:
    """id[Int] with explicit refinement argument."""
    return """
def main (args:Int) : Unit {
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id[Int]{\\n -> n > 0} x;
    print (y)
}
"""


def test_parametric_explicit_type_implicit_refinement_compiles():
    """forall t in type; p only from t<p>."""
    source = f"""
{ID_EXPLICIT_TYPE_IMPLICIT_REF}
{_main_id_int_explicit_app()}
"""
    assert check_compile(source, st_top)


def test_parametric_explicit_type_explicit_refinement_compiles():
    """forall t and forall <p> in type; same term shape as implicit-ref variant."""
    source = f"""
{ID_EXPLICIT_TYPE_EXPLICIT_REF}
{_main_id_int_explicit_app()}
"""
    assert check_compile(source, st_top)


def test_parametric_implicit_type_implicit_refinement_compiles():
    """Free t and t<p> in type; body is plain \\x -> x."""
    source = f"""
{ID_IMPLICIT_TYPE_IMPLICIT_REF}
{_main_id_int_implicit_app()}
"""
    assert check_compile(source, st_top)


def test_parametric_rejects_mismatched_predicate():
    """Output refinement must follow the argument (explicit-type / implicit-ref id)."""
    source = f"""
{ID_EXPLICIT_TYPE_IMPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y < 0 = id[Int] x;
    print (y)
}}
"""
    assert not check_compile(source, st_top)


def test_parametric_rejects_stricter_result_after_chained_id():
    """Chained id cannot justify a strictly stronger predicate."""
    source = f"""
{ID_EXPLICIT_TYPE_IMPLICIT_REF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 7;
    y : Int | y > 0 = id[Int] x;
    z : Int | z > 10 = id[Int] y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# maxI on Int – explicit forall <p> vs implicit refinement (no forall <p> in type)
# ---------------------------------------------------------------------------

# No type-level forall; refinement quantifier explicit (Int monomorphic).
MAXI_EXPLICIT_FORALL_P = (
    "def maxI : forall <p : Int -> Bool>, (x : Int<p>) -> (y : Int<p>) -> Int<p> = "
    "Λ < p : Int -> Bool > => \\x -> \\y -> if x < y then y else x;"
)

MAXI_IMPLICIT_REF = "def maxI : (x : Int<p>) -> (y : Int<p>) -> Int<p> = \\x -> \\y -> if x < y then y else x;"


def test_maxI_explicit_forall_p_compiles():
    """forall <p> on Int only; no type polymorphism; Λ < p => in term."""
    source = f"""
{MAXI_EXPLICIT_FORALL_P}

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


# ---------------------------------------------------------------------------
# const – refinement carried from first argument (implicit p via | p x)
# ---------------------------------------------------------------------------

CONST_DEF = "def const : (x : t | p x) -> (y : t) -> {v : t | p v} = \\x -> \\y -> x;"


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
# Wrapper: implicit type t from (x : t<p>); refinement application on id
# ---------------------------------------------------------------------------

WRAP_DEF = "def wrap : (x : t<p>) -> t<p> = \\x -> id[t]{\\v -> v == x} x;"


def test_wrapper_around_explicit_type_id():
    source_ok = f"""
{ID_EXPLICIT_TYPE_IMPLICIT_REF}
{WRAP_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 4;
    b : Int | b > 0 = wrap[Int] a;
    print (b)
}}
"""
    source_bad = f"""
{ID_EXPLICIT_TYPE_IMPLICIT_REF}
{WRAP_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b > 10 = wrap[Int] a;
    print (b)
}}
"""
    assert check_compile(source_ok, st_top)
    assert not check_compile(source_bad, st_top)
