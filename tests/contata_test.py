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
from aeon.synthesis.modules.contata.cata import BOOL, INT, Example, MemberSig


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


def test_cata_none_when_out_of_size_budget():
    """No body within the size budget ⇒ ``None`` (mutual even/odd needs the
    base/recursive conditional, unreachable at ``max_size=1``)."""
    members = [MemberSig("even", INT, BOOL), MemberSig("odd", INT, BOOL)]
    assert synthesize_group(members, _even_odd_examples(4), max_size=1) is None
