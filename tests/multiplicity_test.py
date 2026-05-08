"""Phase 1 — Multiplicity (QTT) infrastructure.

These tests verify:

1. The semiring algebra (`add`, `mul`) behaves as Atkey 2018 specifies.
2. The grammar accepts the new ``MULT`` prefix on parameters
   (`(1 x:T)`, `(0 x:T)`, `(omega x:T)` and the unicode `ω` form), on
   let-binders (`let 1 x = …`), and on let-binders with a type
   annotation.
3. The parsed multiplicity reaches the relevant AST nodes
   (`Definition.arg_multiplicities`, `SLet.multiplicity`,
   `SRec.multiplicity`) and survives desugaring/lowering down to
   ``AbstractionType.multiplicity``.
4. Programs that *omit* multiplicities continue to default to
   ``MOmega``: there is no behavioural change for existing code.

The actual linearity check that *consumes* these annotations is a
follow-up phase. For now the type-checker treats ``MOmega`` everywhere
and the new fields are inert.
"""

from __future__ import annotations

from aeon.core.bind import bind_ids
from aeon.core.multiplicity import M0, M1, MOmega, Multiplicity, add, from_token, mul
from aeon.core.terms import Rec
from aeon.core.types import AbstractionType
from aeon.elaboration import elaborate
from aeon.sugar.desugar import desugar
from aeon.sugar.lowering import lower_to_core, lower_to_core_context
from aeon.sugar.parser import parse_program


# ---------------------------------------------------------------------------
# Semiring laws
# ---------------------------------------------------------------------------


def test_add_zero_is_identity():
    for m in (M0, M1, MOmega):
        assert add(M0, m) is m
        assert add(m, M0) is m


def test_add_one_plus_one_saturates_to_omega():
    assert add(M1, M1) is MOmega


def test_add_omega_is_absorbing_for_nonzero():
    assert add(MOmega, M1) is MOmega
    assert add(M1, MOmega) is MOmega
    assert add(MOmega, MOmega) is MOmega


def test_mul_zero_is_absorbing():
    for m in (M0, M1, MOmega):
        assert mul(M0, m) is M0
        assert mul(m, M0) is M0


def test_mul_one_is_identity():
    for m in (M0, M1, MOmega):
        assert mul(M1, m) is m
        assert mul(m, M1) is m


def test_mul_omega_omega():
    assert mul(MOmega, MOmega) is MOmega


# ---------------------------------------------------------------------------
# from_token
# ---------------------------------------------------------------------------


def test_from_token_accepts_canonical_forms():
    assert from_token("0") is M0
    assert from_token("1") is M1
    assert from_token("omega") is MOmega
    assert from_token("ω") is MOmega


def test_from_token_rejects_garbage():
    import pytest

    with pytest.raises(ValueError):
        from_token("two")


# ---------------------------------------------------------------------------
# Grammar / parser plumbing
# ---------------------------------------------------------------------------


def test_parser_records_arg_multiplicities():
    src = """
def f (1 x: Int) (y: Int) (0 z: Int) : Int = x;
"""
    prog = parse_program(src)
    f = next(d for d in prog.definitions if d.name.name == "f")
    assert f.arg_multiplicities == (M1, MOmega, M0)


def test_parser_omitting_multiplicity_defaults_to_omega():
    src = """
def f (x: Int) (y: Int) : Int = x;
"""
    prog = parse_program(src)
    f = next(d for d in prog.definitions if d.name.name == "f")
    assert f.arg_multiplicities == (MOmega, MOmega)


def test_parser_omega_unicode_is_accepted():
    src = """
def f (ω x: Int) : Int = x;
"""
    prog = parse_program(src)
    f = next(d for d in prog.definitions if d.name.name == "f")
    assert f.arg_multiplicities == (MOmega,)


def test_parser_records_mult_let_e():
    """`let 1 x = e in body` records multiplicity on the SLet node."""
    from aeon.sugar.program import SLet, SRec

    src = """
def main (i: Int) : Int =
    let 1 a = 5 in
    let b = a in
    b;
"""
    prog = parse_program(src)
    main = next(d for d in prog.definitions if d.name.name == "main")
    body = main.body

    # Walk SLet/SRec chain looking for `a` and `b`.
    binders: dict[str, Multiplicity] = {}
    cur = body
    while isinstance(cur, (SLet, SRec)):
        binders[cur.var_name.name] = cur.multiplicity
        cur = cur.body
    assert binders["a"] is M1
    assert binders["b"] is MOmega


def test_parser_records_mult_rec_e():
    """`let MULT x : T = …` records on SRec."""
    from aeon.sugar.program import SLet, SRec

    src = """
def main (i: Int) : Int =
    let 1 a : Int = 5 in
    a;
"""
    prog = parse_program(src)
    main = next(d for d in prog.definitions if d.name.name == "main")
    cur = main.body
    while isinstance(cur, (SLet, SRec)):
        if cur.var_name.name == "a":
            assert isinstance(cur, SRec)
            assert cur.multiplicity is M1
            return
        cur = cur.body
    assert False, "no binder for `a` found"


# ---------------------------------------------------------------------------
# Desugaring / lowering preservation
# ---------------------------------------------------------------------------


def _find_rec(t, name: str):
    if isinstance(t, Rec):
        if t.var_name.name == name:
            return t
        return _find_rec(t.var_value, name) or _find_rec(t.body, name)
    return None


def test_arg_multiplicity_reaches_core_abstraction_type():
    """A `(1 x: T)` parameter survives desugaring + lowering and ends up
    on the corresponding ``AbstractionType.multiplicity``."""
    src = """
def f (1 x: Int) : Int = x;
def main (_:Int) : Int = f 5;
"""
    prog = parse_program(src)
    desugared = desugar(prog, is_main_hole=False)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core = bind_ids(typing_ctx, core)

    f_rec = _find_rec(core, "f")
    assert f_rec is not None
    assert isinstance(f_rec.var_type, AbstractionType)
    assert f_rec.var_type.multiplicity is M1


def test_omitted_multiplicity_lowers_to_omega():
    """Existing-style programs (no multiplicity) lower to ``MOmega`` —
    no behavioural change."""
    src = """
def f (x: Int) : Int = x;
def main (_:Int) : Int = f 5;
"""
    prog = parse_program(src)
    desugared = desugar(prog, is_main_hole=False)
    sterm = elaborate(desugared.elabcontext, desugared.program)
    core = lower_to_core(sterm)
    typing_ctx = lower_to_core_context(desugared.elabcontext)
    typing_ctx, core = bind_ids(typing_ctx, core)

    f_rec = _find_rec(core, "f")
    assert f_rec is not None
    assert isinstance(f_rec.var_type, AbstractionType)
    assert f_rec.var_type.multiplicity is MOmega
