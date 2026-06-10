"""Regression tests for polymorphic uninterpreted functions reaching the SMT layer.

Before this work, `monomorphic_type` eagerly substituted all TypeVars in
uninterpreted binders with `Int`, and `implication_constraint` for
`TypePolymorphism` returned the constraint unchanged unless a
`reflected_impl` was supplied. Together those meant `forall a, (x:a) -> a
:= uninterpreted` collapsed to a monomorphic `(x:Int) -> Int` and could
not satisfy any other instantiation. These tests pin the corrected flow.
"""

from __future__ import annotations

from aeon.sugar.ast_helpers import st_top
from tests.driver import check_compile


def test_polymorphic_uf_at_base_type():
    """A polymorphic uninterpreted function specialises to ``Int`` correctly."""
    source = """
def my_id : forall a:B, (x: a) -> a := uninterpreted

def use_int (n: Int) : {r: Int | r = my_id n} :=
    native "n" ;
"""
    assert check_compile(source, st_top)


def test_monomorphic_uncurried_uf_congruence():
    """A multi-argument *monomorphic* uninterpreted function reaches the SMT
    layer and the solver applies function congruence through it.

    ``add2`` is already monomorphic, so no specialisation twin is minted;
    it flows straight through ``flatten`` into each ``CanonicConstraint``'s
    ``functions`` and is uncurried into a 2-ary Z3 ``Function`` by
    ``mk_funs``. With premise ``c = a`` the solver must discharge
    ``add2 c b = add2 a b`` purely by congruence (issue #299).
    """
    source = """
def add2 : (x: Int) -> (y: Int) -> Int := uninterpreted

def go (a: Int) (b: Int) (c: {z: Int | z = a}) : {n: Int | n = add2 a b} :=
    let r : {y: Int | y = add2 c b} := native "0" in
    r ;
"""
    assert check_compile(source, st_top)


def test_monomorphic_uncurried_uf_no_spurious_congruence():
    """Without a premise linking the arguments, the solver must *not* assume
    ``add2 a b = add2 c b``. Locks in that the uncurried monomorphic
    declaration is interpreted soundly, not collapsed to a constant.
    """
    source = """
def add2 : (x: Int) -> (y: Int) -> Int := uninterpreted

def go (a: Int) (b: Int) (c: Int) : {n: Int | n = add2 a b} :=
    let r : {y: Int | y = add2 c b} := native "0" in
    r ;
"""
    assert not check_compile(source, st_top)


def test_polymorphic_uf_at_user_type():
    """The same polymorphic UF specialises to a user-declared opaque sort."""
    source = """
type T

def my_id : forall a:B, (x: a) -> a := uninterpreted

def use_t (t: T) : {r: T | r = my_id t} :=
    native "t" ;
"""
    assert check_compile(source, st_top)


def test_polymorphic_uf_at_two_instantiations_in_one_file():
    """Different call-sites with different concrete types coexist."""
    source = """
type T

def my_id : forall a:B, (x: a) -> a := uninterpreted

def use_int (n: Int) : {r: Int | r = my_id n} :=
    native "n" ;

def use_t (t: T) : {r: T | r = my_id t} :=
    native "t" ;
"""
    assert check_compile(source, st_top)


def test_polymorphic_uf_chained_in_refinement():
    """``feats (my_id x) = feats x`` is provable when callsite returns ``x``."""
    source = """
type T

def my_id : forall a:B, (x: a) -> a := uninterpreted
def feats : (t: T) -> Int := uninterpreted

def go (t: T) : {n: Int | n = feats (my_id t)} :=
    let r : {x: T | x = my_id t} := native "t" in
    let n : {y: Int | y = feats r} := native "0" in
    n ;
"""
    assert check_compile(source, st_top)


def test_auto_generated_projection_in_refinement():
    """``Pair_mk_fst`` (auto-generated from ``inductive Pair a b | mk``)
    can be used inside a refinement and the SMT solver discharges
    chained equalities through it.
    """
    source = """
type Dataset

inductive Pair a b
| mk (fst:a) (snd:b) : (Pair a b)

def feats : (ds: Dataset) -> Int := uninterpreted

def split (ds: Dataset) :
    {p: (Pair Dataset Dataset)
        | feats (Pair_mk_fst p) = feats ds
       && feats (Pair_mk_snd p) = feats ds} :=
    native "('Pair_mk', ds, ds)"

def fst_of (p: (Pair Dataset Dataset)) : {d: Dataset | d = Pair_mk_fst p} :=
    native "p[1]"

def good (ds: Dataset) : {n: Int | n = feats ds} :=
    let p := split ds in
    let t := fst_of p in
    let r : {x: Int | x = feats t} := native "0" in
    r ;
"""
    assert check_compile(source, st_top)


def test_parametric_inductive_two_instantiations():
    """Different parametric ``Pair`` instantiations get distinct sorts."""
    source = """
type Dataset

inductive Pair a b
| mk (fst:a) (snd:b) : (Pair a b)

def fst_dataset (p: (Pair Dataset Dataset)) : {d: Dataset | d = Pair_mk_fst p} :=
    native "p[1]"

def fst_int (p: (Pair Int Int)) : {n: Int | n = Pair_mk_fst p} :=
    native "p[1]"
"""
    assert check_compile(source, st_top)


def test_same_pair_instantiation_variables_share_sort():
    """Two variables of ``Pair Dataset Dataset`` share a Z3 sort, so a
    premise ``q = p`` is usable by the SMT solver to discharge a goal
    ``feats (Pair_mk_fst q) = feats (Pair_mk_fst p)`` (function
    congruence). Pre-PR, the ``flatten`` Implication path stamped each
    binding with a fresh ID, putting ``p`` and ``q`` in *distinct* Z3
    sorts even when typed at the same Aeon type — this regression test
    pins the corrected, deterministic mangling.
    """
    source = """
type Dataset

inductive Pair a b
| mk (fst:a) (snd:b) : (Pair a b)

def feats : (ds: Dataset) -> Int := uninterpreted

def use (p: (Pair Dataset Dataset)) (q: {x: (Pair Dataset Dataset) | x = p})
        : {n: Int | n = feats (Pair_mk_fst p)} :=
    let r : {y: Int | y = feats (Pair_mk_fst q)} := native "0" in
    r ;
"""
    assert check_compile(source, st_top)


def test_unrelated_pair_projections_not_equated():
    """``Pair_mk_fst p = Pair_mk_fst q`` is *not* assumed for two
    independent ``Pair Int Int`` arguments. Without a premise linking
    ``p`` and ``q`` the SMT solver correctly refuses to discharge a
    goal that claims this equality. Locks in the specialisation
    soundness: distinct call sites of ``Pair_mk_fst`` produce distinct
    abstract values; the solver only equates them under explicit
    premises (as in ``test_same_pair_instantiation_variables_share_sort``).
    """
    source = """
inductive Pair a b
| mk (fst:a) (snd:b) : (Pair a b)

def feats : (n: Int) -> Int := uninterpreted

def consume (n: Int) (m: {x: Int | x = n}) : Int := 0

def bad (p: (Pair Int Int)) (q: (Pair Int Int)) : Int :=
    consume (feats (Pair_mk_fst p)) (feats (Pair_mk_fst q)) ;
"""
    assert not check_compile(source, st_top)
