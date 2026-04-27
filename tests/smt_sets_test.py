"""Tests for SMT Set support in refinement types."""

from __future__ import annotations

from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidVar
from aeon.core.types import t_int, t_set
from aeon.sugar.ast_helpers import st_top
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Implication, LiquidConstraint
from tests.driver import check_compile
from aeon.utils.name import Name


# ---------------------------------------------------------------------------
# SMT-level set constraint tests
# ---------------------------------------------------------------------------


def _imp(name: str, base, pred, seq):
    return Implication(Name(name), base, pred, seq)


def test_set_empty_is_subset_of_any():
    """Set_sub(Set_empty, s) is always true."""
    s = Name("s")
    c = _imp(
        "s",
        t_set,
        LiquidLiteralBool(True),
        LiquidConstraint(LiquidApp(Name("Set_sub", 0), [LiquidVar(Name("Set_empty", 0)), LiquidVar(s)])),
    )
    assert smt_valid(c)


def test_set_member_after_singleton():
    """Set_mem(x, Set_sng(x)) is always true."""
    x = Name("x")
    c = _imp(
        "x",
        t_int,
        LiquidLiteralBool(True),
        LiquidConstraint(LiquidApp(Name("Set_mem", 0), [LiquidVar(x), LiquidApp(Name("Set_sng", 0), [LiquidVar(x)])])),
    )
    assert smt_valid(c)


def test_set_union_contains_both():
    """Set_mem(x, Set_cup(Set_sng(x), s)) is always true."""
    x = Name("x")
    s = Name("s")
    sng_x = LiquidApp(Name("Set_sng", 0), [LiquidVar(x)])
    union = LiquidApp(Name("Set_cup", 0), [sng_x, LiquidVar(s)])
    mem = LiquidApp(Name("Set_mem", 0), [LiquidVar(x), union])
    c = _imp(
        "x",
        t_int,
        LiquidLiteralBool(True),
        _imp("s", t_set, LiquidLiteralBool(True), LiquidConstraint(mem)),
    )
    assert smt_valid(c)


def test_set_difference_removes_element():
    """Set_mem(x, Set_dif(Set_sng(x), Set_sng(x))) is always false."""
    x = Name("x")
    sng_x = LiquidApp(Name("Set_sng", 0), [LiquidVar(x)])
    diff = LiquidApp(Name("Set_dif", 0), [sng_x, sng_x])
    mem = LiquidApp(Name("Set_mem", 0), [LiquidVar(x), diff])
    not_mem = LiquidApp(Name("!", 0), [mem])
    c = _imp("x", t_int, LiquidLiteralBool(True), LiquidConstraint(not_mem))
    assert smt_valid(c)


def test_set_intersection_subset():
    """Set_sub(Set_cap(a, b), a) is always true."""
    a = Name("a")
    b = Name("b")
    cap = LiquidApp(Name("Set_cap", 0), [LiquidVar(a), LiquidVar(b)])
    sub = LiquidApp(Name("Set_sub", 0), [cap, LiquidVar(a)])
    c = _imp(
        "a",
        t_set,
        LiquidLiteralBool(True),
        _imp("b", t_set, LiquidLiteralBool(True), LiquidConstraint(sub)),
    )
    assert smt_valid(c)


def test_set_equality_union_commutative():
    """Set_cup(a, b) == Set_cup(b, a)."""
    a = Name("a")
    b = Name("b")
    cup_ab = LiquidApp(Name("Set_cup", 0), [LiquidVar(a), LiquidVar(b)])
    cup_ba = LiquidApp(Name("Set_cup", 0), [LiquidVar(b), LiquidVar(a)])
    eq = LiquidApp(Name("==", 0), [cup_ab, cup_ba])
    c = _imp(
        "a",
        t_set,
        LiquidLiteralBool(True),
        _imp("b", t_set, LiquidLiteralBool(True), LiquidConstraint(eq)),
    )
    assert smt_valid(c)


def test_set_invalid_constraint_rejected():
    """Set_sub(a, Set_empty) should NOT be valid for all a."""
    a = Name("a")
    sub = LiquidApp(Name("Set_sub", 0), [LiquidVar(a), LiquidVar(Name("Set_empty", 0))])
    c = _imp("a", t_set, LiquidLiteralBool(True), LiquidConstraint(sub))
    assert not smt_valid(c)


# ---------------------------------------------------------------------------
# End-to-end Aeon program tests with sets
# ---------------------------------------------------------------------------


def test_set_empty_list():
    """Verify a list with an uninterpreted 'elts' measure and Set_empty."""
    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted

def empty : {l:IntList | elts l == Set_empty} = native "[]"

def main (_:Int) : Unit = print(empty)
"""
    assert check_compile(code, st_top)


def test_set_cons_union():
    """Verify cons adds an element to the set."""
    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted

def empty : {l:IntList | elts l == Set_empty} = native "[]"

def cons (x:Int) (xs:IntList) : {l:IntList | elts l == Set_cup (Set_sng x) (elts xs)} =
    native "[x] + xs"

def main (_:Int) : Unit =
    a = cons 1 empty;
    print(a)
"""
    assert check_compile(code, st_top)


def test_set_append_is_union():
    """Verify append is the union of elements."""
    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted

def empty : {l:IntList | elts l == Set_empty} = native "[]"

def cons (x:Int) (xs:IntList) : {l:IntList | elts l == Set_cup (Set_sng x) (elts xs)} =
    native "[x] + xs"

def append (xs:IntList) (ys:IntList) : {l:IntList | elts l == Set_cup (elts xs) (elts ys)} =
    native "xs + ys"

def main (_:Int) : Unit =
    a = cons 1 empty;
    b = cons 2 empty;
    c = append a b;
    print(c)
"""
    assert check_compile(code, st_top)


def test_set_sort_is_permutation():
    """Sort preserves elements (permutation property)."""
    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted

def sort (xs:IntList) : {l:IntList | elts l == elts xs} = native "sorted(xs)"

def main (_:Int) : Unit =
    print(0)
"""
    assert check_compile(code, st_top)


def test_set_contains_faithful():
    """Membership check is faithful to the logical set."""
    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted

def contains (x:Int) (xs:IntList) : {b:Bool | b == Set_mem x (elts xs)} =
    native "x in xs"

def main (_:Int) : Unit =
    print(0)
"""
    assert check_compile(code, st_top)


def test_set_filter_subset():
    """Filter returns a subset."""
    code = """
type IntList

def elts : (l:IntList) -> Set = uninterpreted

def myfilter (xs:IntList) : {l:IntList | Set_sub (elts l) (elts xs)} =
    native "[x for x in xs if x > 0]"

def main (_:Int) : Unit = print(0)
"""
    assert check_compile(code, st_top)
