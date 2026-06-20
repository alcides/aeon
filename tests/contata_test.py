"""Tests for the Contata CATA version space (issue #397).

A genuine Constraint-Annotated Tree Automaton: candidate bodies are denoted
symbolically as z3 expressions over the functions under synthesis (uninterpreted
functions = the constraint annotation), accepted by SMT against the spec, with
the well-foundedness side condition and MinTree extraction. Unlike
enumerate-and-typecheck, this synthesizes genuinely mutually-recursive programs
(even/odd) from a relational/example spec.
"""

from __future__ import annotations

from aeon.core.terms import Application, If, Term, Var
from aeon.synthesis.modules.contata import synthesize_group
from aeon.synthesis.modules.contata.cata import BOOL, INT, LIST, Example, MemberSig


def _mentions(term: Term, name: str) -> bool:
    match term:
        case Var(n):
            return n.name == name
        case Application(fun, arg):
            return _mentions(fun, name) or _mentions(arg, name)
        case If(c, th, el):
            return _mentions(c, name) or _mentions(th, name) or _mentions(el, name)
        case _:
            return False


def _even_odd_examples(upto: int) -> list[Example]:
    ex: list[Example] = []
    for n in range(upto):
        ex.append(Example("even", n, n % 2 == 0))
        ex.append(Example("odd", n, n % 2 == 1))
    return ex


def test_cata_synthesizes_mutual_even_odd():
    """The MR flagship: co-synthesize even/odd from examples. Each body must be a
    base/recursive conditional that calls its *sibling* — the genuinely
    mutually-recursive solution the version space accepts under SMT."""
    members = [MemberSig("even", INT, BOOL), MemberSig("odd", INT, BOOL)]
    res = synthesize_group(members, _even_odd_examples(5), max_size=3)
    assert res is not None
    even, odd = res.bodies["even"], res.bodies["odd"]
    assert isinstance(even, If) and isinstance(odd, If)
    assert _mentions(even, "odd"), even  # even calls odd (mutual)
    assert _mentions(odd, "even"), odd  # odd calls even (mutual)


def test_cata_recovers_evaluable_definitions():
    """The synthesized bodies, assembled into a real mutual program, evaluate to
    the specified outputs (the version space's solution is genuinely correct, not
    just SMT-consistent)."""
    members = [MemberSig("even", INT, BOOL), MemberSig("odd", INT, BOOL)]
    res = synthesize_group(members, _even_odd_examples(5), max_size=3)
    assert res is not None
    # Render and evaluate via the full driver to confirm behaviour.
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.core.pprint import pretty_print  # noqa: F401  (ensure import path exists)

    def render(body: Term) -> str:
        match body:
            case If(c, th, el):
                return f"if {render(c)} then {render(th)} else {render(el)}"
            case Application(Application(Var(op), a), b):
                surface = {"==": "=", "!=": "!="}.get(op.name, op.name)
                return f"({render(a)} {surface} {render(b)})"
            case Application(Var(f), a):
                return f"{f.name} ({render(a)})"
            case Var(n):
                return n.name
            case _:
                from aeon.core.terms import Literal

                assert isinstance(body, Literal)
                return str(body.value).lower()

    src = f"""
mutual
  def even (x: {{v:Int | v >= 0}}) : Bool decreasing_by [x] := {render(res.bodies["even"])}
  def odd  (x: {{v:Int | v >= 0}}) : Bool decreasing_by [x] := {render(res.bodies["odd"])}
end
def main (a: Int) : Int := if even 6 then (if odd 5 then 1 else 0) else 0;
"""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=0, no_main=False)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code=src, filename="<t>") == []
    assert d.run() == 1  # even 6 and odd 5


def test_cata_synthesizes_predicate():
    """A non-recursive relational predicate: f(0)=true, else false ⇒ ``x == 0``."""
    members = [MemberSig("f", INT, BOOL)]
    ex = [Example("f", 0, True)] + [Example("f", n, False) for n in range(1, 4)]
    res = synthesize_group(members, ex, max_size=3)
    assert res is not None
    assert _mentions(res.bodies["f"], "x")


def test_cata_synthesizes_list_length_pds():
    """The PDS (partial-data-structure) category: synthesize ``length`` over
    ``List Int`` from trace-closed examples. The version space must form the
    base/recursive conditional ``if isEmpty xs then 0 else 1 + length (tail xs)``
    — a recursive call under an operator, on the structurally-smaller tail (the
    well-founded measure is list length)."""
    members = [MemberSig("length", LIST, INT)]
    ex = [
        Example("length", (), 0),
        Example("length", (3,), 1),
        Example("length", (2, 3), 2),
        Example("length", (1, 2, 3), 3),
    ]
    res = synthesize_group(members, ex, max_size=4)
    assert res is not None
    body = res.bodies["length"]
    assert isinstance(body, If)
    assert _mentions(body, "length"), body  # genuinely recursive
    assert _mentions(body, "isEmpty"), body  # base/recursive split on emptiness


def test_contata_backend_fills_predicate_from_examples():
    """The ``-s contata`` CLI backend: the version space synthesises a hole from
    its ``@example`` I/O facts, rebinds the body onto real in-scope names
    (parameter, operators monomorphised at Int), discharges it through the liquid
    typechecker, and the filled program type checks and evaluates."""
    from aeon.core.types import Top
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.typechecking.typeinfer import check_type

    src = """
@example(isZero 0 = true)
@example(isZero 1 = false)
@example(isZero 2 = false)
def isZero (x: {v:Int | v >= 0}) : Bool := ?hole;
def main (a: Int) : Int := if isZero 0 then (if isZero 3 then 1 else 0) else 9;
"""
    cfg = AeonConfig(synthesizer="contata", synthesis_ui=SilentSynthesisUI(), synthesis_budget=5, no_main=False)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code=src, filename="<t>") == []
    assert d.has_synth()
    d.synth()
    assert check_type(d.typing_ctx, d.core, Top())  # hole filled, program well-typed
    assert d.run() == 0  # isZero 0 = true and isZero 3 = false


def test_contata_cosynthesizes_mutual_group_from_examples():
    """The MR flagship through the CLI: a ``mutual`` block whose members are
    holes specified only by ``@example`` facts is co-synthesised by the version
    space in one SMT query — each body calls its sibling. The old per-member
    loop could not converge on this; the version-space fast path does."""
    from aeon.core.types import Top
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.typechecking.typeinfer import check_type

    src = """
mutual
  @example(even 0 = true)
  @example(even 1 = false)
  @example(even 2 = true)
  @example(even 3 = false)
  def even (x: {v:Int | v >= 0}) : Bool decreasing_by [x] := ?he;
  @example(odd 0 = false)
  @example(odd 1 = true)
  @example(odd 2 = false)
  @example(odd 3 = true)
  def odd (x: {v:Int | v >= 0}) : Bool decreasing_by [x] := ?ho;
end
def main (a: Int) : Int := if even 6 then (if odd 5 then 1 else 0) else 0;
"""
    cfg = AeonConfig(synthesizer="contata", synthesis_ui=SilentSynthesisUI(), synthesis_budget=10, no_main=False)
    d = AeonDriver(cfg)
    assert d.parse(aeon_code=src, filename="<t>") == []
    assert d.has_synth()
    d.synth()
    assert check_type(d.typing_ctx, d.core, Top())  # both holes filled, group well-typed
    assert d.run() == 1  # even 6 and odd 5 both hold


def test_cata_none_when_out_of_size_budget():
    """No body within the size budget ⇒ ``None`` (mutual even/odd needs the
    base/recursive conditional, unreachable at ``max_size=1``)."""
    members = [MemberSig("even", INT, BOOL), MemberSig("odd", INT, BOOL)]
    assert synthesize_group(members, _even_odd_examples(4), max_size=1) is None
