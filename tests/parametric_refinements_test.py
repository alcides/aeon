from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

ID_DEF = (
    "def id : forall t : B, forall <p : t -> Bool>,"
    " (x : t | p x) -> {v : t | p v} = Λ t : B => \\x -> x;"
)

CONST_DEF = (
    "def const : forall t : B, forall <p : t -> Bool>,"
    " (x : t | p x) -> (y : t) -> {v : t | p v} = Λ t : B => \\x -> \\y -> x;"
)

# ---------------------------------------------------------------------------
# id – basic identity with explicit predicate
# ---------------------------------------------------------------------------


def test_id_positive_int():
    """id propagates a positive-integer predicate."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y > 0 = id[Int]{{\\n -> n > 0}} x;
    print (y)
}}
"""
    assert check_compile(source, st_top)


def test_id_rejects_mismatched_predicate():
    """Passing a positive value with a negative predicate must fail."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 3;
    y : Int | y < 0 = id[Int]{{\\n -> n < 0}} x;
    print (y)
}}
"""
    assert not check_compile(source, st_top)


def test_id_bool_predicate():
    """id works over Bool with an identity predicate (p x = x)."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    b : Bool | b == true = true;
    r : Bool | r == true = id[Bool]{{\\v -> v}} b;
    print (r)
}}
"""
    assert check_compile(source, st_top)


def test_id_bool_predicate_rejects_false():
    """id with 'must be true' predicate should reject a false literal."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    b : Bool | b == false = false;
    r : Bool | r == true = id[Bool]{{\\v -> v}} b;
    print (r)
}}
"""
    assert not check_compile(source, st_top)


def test_id_equality_predicate():
    """Predicate that constrains exact value is preserved end-to-end."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x == 42 = 42;
    y : Int | y == 42 = id[Int]{{\\n -> n == 42}} x;
    print (y)
}}
"""
    assert check_compile(source, st_top)


def test_id_non_negative_predicate():
    """Predicate 'n >= 0' is preserved by id."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x >= 0 = 0;
    y : Int | y >= 0 = id[Int]{{\\n -> n >= 0}} x;
    print (y)
}}
"""
    assert check_compile(source, st_top)


# ---------------------------------------------------------------------------
# const – first argument is returned, predicate must follow
# ---------------------------------------------------------------------------


def test_const_positive():
    """const returns x ignoring y; output must still satisfy predicate on x."""
    source = f"""
{CONST_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 5;
    r : Int | r > 0 = const[Int]{{\\n -> n > 0}} x 99;
    print (r)
}}
"""
    assert check_compile(source, st_top)


def test_const_rejects_wrong_predicate_on_result():
    """const: predicate claimed on result does not match predicate on x."""
    source = f"""
{CONST_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 5;
    r : Int | r < 0 = const[Int]{{\\n -> n > 0}} x 99;
    print (r)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# Chained calls – predicate flows through two id applications
# ---------------------------------------------------------------------------


def test_id_chained():
    """Applying id twice with the same predicate still type-checks."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 7;
    y : Int | y > 0 = id[Int]{{\\n -> n > 0}} x;
    z : Int | z > 0 = id[Int]{{\\n -> n > 0}} y;
    print (z)
}}
"""
    assert check_compile(source, st_top)


def test_id_chained_predicate_weakening_rejects():
    """Second call uses a stricter predicate not guaranteed by the first."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    x : Int | x > 0 = 7;
    y : Int | y > 0 = id[Int]{{\\n -> n > 0}} x;
    z : Int | z > 10 = id[Int]{{\\n -> n > 10}} y;
    print (z)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# Predicate-polymorphic wrapper - user-defined wrapper around id
# ---------------------------------------------------------------------------


def test_wrapper_around_id_positive():
    """A user wrapper that calls id internally still propagates the predicate."""
    source = f"""
{ID_DEF}

def wrap : forall t : B, forall <p : t -> Bool>, (x : t | p x) -> {{v : t | p v}} =
    Λ t : B => \\x -> id[t]{{\\v -> v == x}} x;

def main (args:Int) : Unit {{
    a : Int | a > 0 = 4;
    b : Int | b > 0 = wrap[Int]{{\\n -> n > 0}} a;
    print (b)
}}
"""
    assert check_compile(source, st_top)


def test_wrapper_around_id_negative():
    """Wrapper claims stronger predicate on result than argument provides."""
    source = f"""
{ID_DEF}

def wrap : forall t : B, forall <p : t -> Bool>, (x : t | p x) -> {{v : t | p v}} =
    Λ t : B => \\x -> id[t]{{\\v -> v == x}} x;

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b > 10 = wrap[Int]{{\\n -> n > 10}} a;
    print (b)
}}
"""
    assert not check_compile(source, st_top)


# ---------------------------------------------------------------------------
# Multiple independent predicate applications in one program
# ---------------------------------------------------------------------------


def test_two_independent_predicates():
    """Two id calls with different predicates in the same function."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b < 0 = 0 - 1;
    ra : Int | ra > 0 = id[Int]{{\\n -> n > 0}} a;
    rb : Int | rb < 0 = id[Int]{{\\n -> n < 0}} b;
    print (ra)
}}
"""
    assert check_compile(source, st_top)


def test_two_independent_predicates_negative():
    """One of the independent uses violates its predicate."""
    source = f"""
{ID_DEF}

def main (args:Int) : Unit {{
    a : Int | a > 0 = 1;
    b : Int | b < 0 = 1;
    ra : Int | ra > 0 = id[Int]{{\\n -> n > 0}} a;
    rb : Int | rb > 0 = id[Int]{{\\n -> n < 0}} b;
    print (ra)
}}
"""
    assert not check_compile(source, st_top)

