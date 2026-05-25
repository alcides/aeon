"""Regression tests for polymorphic uninterpreted functions reaching the SMT layer.

Before this work, `monomorphic_type` eagerly substituted all TypeVars in
uninterpreted binders with `Int`, and `implication_constraint` for
`TypePolymorphism` returned the constraint unchanged unless a
`reflected_impl` was supplied. Together those meant `forall a, (x:a) -> a
= uninterpreted` collapsed to a monomorphic `(x:Int) -> Int` and could
not satisfy any other instantiation. These tests pin the corrected flow.
"""

from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile


def test_polymorphic_uf_at_base_type():
    """A polymorphic uninterpreted function specialises to ``Int`` correctly."""
    source = """
def my_id : forall a:B, (x: a) -> a = uninterpreted

def use_int (n: Int) : {r: Int | r == my_id n} =
    native "n" ;
"""
    assert check_compile(source, st_top)


def test_polymorphic_uf_at_user_type():
    """The same polymorphic UF specialises to a user-declared opaque sort."""
    source = """
type T

def my_id : forall a:B, (x: a) -> a = uninterpreted

def use_t (t: T) : {r: T | r == my_id t} =
    native "t" ;
"""
    assert check_compile(source, st_top)


def test_polymorphic_uf_at_two_instantiations_in_one_file():
    """Different call-sites with different concrete types coexist."""
    source = """
type T

def my_id : forall a:B, (x: a) -> a = uninterpreted

def use_int (n: Int) : {r: Int | r == my_id n} =
    native "n" ;

def use_t (t: T) : {r: T | r == my_id t} =
    native "t" ;
"""
    assert check_compile(source, st_top)


def test_polymorphic_uf_chained_in_refinement():
    """``feats (my_id x) == feats x`` is provable when callsite returns ``x``."""
    source = """
type T

def my_id : forall a:B, (x: a) -> a = uninterpreted
def feats : (t: T) -> Int = uninterpreted

def go (t: T) : {n: Int | n == feats (my_id t)} =
    let r : {x: T | x == my_id t} = native "t" in
    let n : {y: Int | y == feats r} = native "0" in
    n ;
"""
    assert check_compile(source, st_top)
