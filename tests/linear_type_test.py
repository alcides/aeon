"""Tests for ``linear type`` declarations (issue #489).

A ``linear type`` marks a type whose values are unique. Where the QTT
multiplicities of issue #441 put the discipline on the *binder* — a plain
``let c := connect "db"`` escapes every check because ``ω`` binders are
never inspected — a linear *type* moves it onto the type itself: every
binder holding such a value must be declared at multiplicity ``1``, so a
resource can no longer be duplicated or dropped by simply omitting the
annotation.

The last group covers the two soundness fixes this feature needed:
refinement-parametric readers over an opaque wrapper (which requires
substitution to descend into type-constructor arguments), and abstract
refinement instantiation actually being enforced.
"""

from __future__ import annotations

from aeon.facade.api import (
    LinearityError,
    LinearTypeNotBoundLinearlyError,
    LinearUsedTooManyTimesError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

MAIN = '\ndef main (args: Int) : Unit := print "ok";\n'

RESOURCE = """
linear type Res

def open_res (x: Int) : Res := native "[]";
def use_res (1 r: Res) : Int := native "0";
def close_res (1 r: Res) : Unit := native "None";
"""


def _parse(source: str):
    setup_logger()
    cfg = AeonConfig(synthesizer="enumerative", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=True)
    return list(AeonDriver(cfg).parse(aeon_code=source))


def _linearity_errors(source: str):
    return [e for e in _parse(source) if isinstance(e, LinearityError)]


# ---------------------------------------------------------------------------
# Declaration and the binder rule
# ---------------------------------------------------------------------------


def test_linear_type_declaration_is_accepted():
    assert _parse(RESOURCE + MAIN) == []


def test_linear_parameter_must_be_declared_at_one():
    src = RESOURCE + "\ndef consume (r: Res) : Unit := close_res r;" + MAIN
    errors = _linearity_errors(src)
    assert len(errors) == 1
    assert isinstance(errors[0], LinearTypeNotBoundLinearlyError)


def test_linear_parameter_at_one_is_accepted():
    src = RESOURCE + "\ndef consume (1 r: Res) : Unit := close_res r;" + MAIN
    assert _linearity_errors(src) == []


def test_let_of_linear_value_must_be_declared_at_one():
    """The hole from issue #489: the value is linear but the binder is ``ω``,
    so nothing used to be checked."""
    src = RESOURCE + "\ndef run (x: Int) : Unit := let r := open_res x in close_res r;" + MAIN
    errors = _linearity_errors(src)
    assert len(errors) == 1
    assert isinstance(errors[0], LinearTypeNotBoundLinearlyError)


def test_let_of_linear_value_at_one_is_accepted():
    src = RESOURCE + "\ndef run (x: Int) : Unit := let 1 r := open_res x in close_res r;" + MAIN
    assert _linearity_errors(src) == []


def test_linear_binder_still_cannot_be_used_twice():
    src = (
        RESOURCE
        + """
def run (1 r: Res) : Int :=
    let 1 a := use_res r in
    use_res r;"""
        + MAIN
    )
    errors = _linearity_errors(src)
    assert any(isinstance(e, LinearUsedTooManyTimesError) for e in errors)


def test_omega_binder_of_unrestricted_type_is_unaffected():
    src = (
        """
type Plain

def mk (x: Int) : Plain := native "[]";
def rd (p: Plain) : Int := native "0";

def run (x: Int) : Int := let p := mk x in rd p + rd p;"""
        + MAIN
    )
    assert _linearity_errors(src) == []


def test_refinement_on_a_linear_type_is_transparent():
    """``{r: Res | ok r}`` is as unique as ``Res``."""
    src = (
        """
linear type Res

def ok : (r: Res) -> Bool := uninterpreted
def open_res (x: Int) : {r: Res | ok r = true} := native "[]";
def close_res (1 r: {r: Res | ok r = true}) : Unit := native "None";

def run (x: Int) : Unit := let r := open_res x in close_res r;"""
        + MAIN
    )
    errors = _linearity_errors(src)
    assert len(errors) == 1
    assert isinstance(errors[0], LinearTypeNotBoundLinearlyError)


def test_parametric_linear_type():
    src = (
        """
linear type Box a

def mk (x: Int) : (Box Int) := native "[]";
def unbox (1 b: (Box Int)) : Int := native "0";

def run (x: Int) : Int := let b := mk x in unbox b;"""
        + MAIN
    )
    errors = _linearity_errors(src)
    assert len(errors) == 1
    assert isinstance(errors[0], LinearTypeNotBoundLinearlyError)


def test_linear_is_still_usable_as_an_identifier():
    """``linear`` is only a keyword in front of ``type``."""
    src = "\ndef linear (x: Int) : Int := x;\ndef f (linear: Int) : Int := linear;" + MAIN
    assert _parse(src) == []


# ---------------------------------------------------------------------------
# Standard-library resource types
# ---------------------------------------------------------------------------


def test_socket_bound_without_one_is_rejected():
    src = (
        """
open Socket

def leak (port: { p: Int | (p >= 0) && (p <= 65535) }) : Unit :=
    let s := stream_socket unit in
    stream_close s;"""
        + MAIN
    )
    assert any(isinstance(e, LinearTypeNotBoundLinearlyError) for e in _linearity_errors(src))


def test_connection_bound_without_one_is_rejected():
    src = (
        """
open Database

def leak (x: Int) : Unit :=
    let c := connect "app.db" in
    close c;"""
        + MAIN
    )
    assert any(isinstance(e, LinearTypeNotBoundLinearlyError) for e in _linearity_errors(src))


def test_rng_bound_without_one_is_rejected():
    src = (
        """
open Random

def leak (seed: Int) : Unit :=
    let g := new_rng seed in
    close_rng g;"""
        + MAIN
    )
    assert any(isinstance(e, LinearTypeNotBoundLinearlyError) for e in _linearity_errors(src))


def test_socket_lifecycle_with_one_still_typechecks():
    src = (
        """
open Socket

def lifecycle (port: { p: Int | (p >= 0) && (p <= 65535) }) : Unit :=
    let 1 s0 := stream_socket unit in
    let 1 s1 := stream_bind (ipv4_addr "127.0.0.1" port) s0 in
    stream_close s1;"""
        + MAIN
    )
    assert _parse(src) == []


# ---------------------------------------------------------------------------
# Refinement-parametric readers over a linear value
# ---------------------------------------------------------------------------

READER = """
open Array

type ArrayGet a

def got_size : (g: (ArrayGet a)) -> Int := uninterpreted

def get_at (1 arr: (Array a<p>)) (i: {n:Int | n >= 0 && n < size arr}) :
    {g: (ArrayGet a<p>) | got_size g = size arr} := native "(arr[i], arr)";
def got_value (g: (ArrayGet a<p>)) : a<p> := native "g[0]";
def got_array (g: (ArrayGet a<p>)) : {r: (Array a<p>) | size r = got_size g} := native "g[1]";

def use_positive (v: {x:Int | x > 0}) : Int := v;
"""


def test_reader_preserves_the_element_refinement():
    """The element predicate rides on ``a<p>`` through the opaque wrapper, so
    the value read out of a positive array is still known to be positive."""
    src = (
        READER
        + """
def read (1 arr: {r: (Array {x:Int | x > 0}) | size r = 3}) : Int :=
    let g := get_at arr 0 in
    use_positive (got_value g);"""
        + MAIN
    )
    assert _parse(src) == []


def test_reader_preserves_the_length_measure():
    """``got_size`` threads ``size`` across the wrapper, so the array handed
    back by the projection still has a known length."""
    src = (
        READER
        + """
def read_twice (1 arr: {r: (Array {x:Int | x > 0}) | size r = 3}) : Int :=
    let g := get_at arr 0 in
    let a := use_positive (got_value g) in
    let 1 back := got_array g in
    let g2 := get_at back 2 in
    a + use_positive (got_value g2);"""
        + MAIN
    )
    assert _parse(src) == []


def test_reader_rejects_an_out_of_range_index():
    src = (
        READER
        + """
def read (1 arr: {r: (Array {x:Int | x > 0}) | size r = 3}) : Int :=
    let g := get_at arr 7 in
    use_positive (got_value g);"""
        + MAIN
    )
    assert _parse(src) != []


def test_reader_does_not_invent_a_refinement():
    """An array with no element guarantee cannot be read as positive."""
    src = (
        READER
        + """
def read (1 arr: {r: (Array Int) | size r = 3}) : Int :=
    let g := get_at arr 0 in
    use_positive (got_value g);"""
        + MAIN
    )
    assert _parse(src) != []


# ---------------------------------------------------------------------------
# Abstract refinement instantiation is enforced
# ---------------------------------------------------------------------------


def test_abstract_refinement_is_not_vacuous():
    """``id2`` may only return a positive value if it was given one. The
    Horn variable standing for ``p`` has to get a single solution across the
    argument and the result, or the call below is accepted vacuously."""
    src = (
        """
def id2 (x: a<p>) : a<p> := x;
def use_positive (v: {x:Int | x > 0}) : Int := v;

def bad (n: Int) : Int := use_positive (id2 n);"""
        + MAIN
    )
    assert _parse(src) != []


def test_abstract_refinement_accepts_a_valid_instantiation():
    src = (
        """
def id2 (x: a<p>) : a<p> := x;
def use_positive (v: {x:Int | x > 0}) : Int := v;

def good (n: {x:Int | x > 0}) : Int := use_positive (id2 n);"""
        + MAIN
    )
    assert _parse(src) == []
