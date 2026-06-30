"""Tests for the type-aware LSP features: position→type index, refinement-aware
completion (Tiers 1–3), inferred-type inlay hints, document symbols and
go-to-definition."""

from __future__ import annotations

import pytest

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp import completion as C
from aeon.lsp import navigation as N
from aeon.lsp.typeindex import build_type_index
from aeon.synthesis.uis.api import SilentSynthesisUI


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #


def analyse(src: str):
    """Parse ``src`` and return ``(driver, type_index, errors)``. The type index
    is built whenever core generation succeeded, even if type checking failed."""
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=1)
    d = AeonDriver(cfg)
    errors = list(d.parse(filename="file:///t.ae", aeon_code=src))
    index = build_type_index(d.typing_ctx, d.core) if getattr(d, "core", None) is not None else None
    return d, index, errors


def labels(comps):
    return [c.label for c in comps]


def by_label(comps, label):
    return next(c for c in comps if c.label == label)


def col_after(src, line0, needle):
    """0-indexed column just past ``needle`` on (0-indexed) ``line0``."""
    text = src.splitlines()[line0]
    return text.index(needle) + len(needle)


# --------------------------------------------------------------------------- #
# Pure helpers: receiver detection, base types, formatting
# --------------------------------------------------------------------------- #


def test_parse_dot_context_simple_identifier():
    line = "    n.dou"
    ctx = C.parse_dot_context(line, len(line))
    assert ctx is not None
    assert ctx.receiver_text == "n"
    assert ctx.prefix == "dou"


def test_parse_dot_context_literal():
    ctx = C.parse_dot_context("1.", 2)
    assert ctx is not None
    assert ctx.receiver_text == "1"
    assert ctx.prefix == ""


def test_parse_dot_context_parenthesised_receiver():
    line = "(1.plus 2)."
    ctx = C.parse_dot_context(line, len(line))
    assert ctx is not None
    assert ctx.receiver_text == "(1.plus 2)"


def test_parse_dot_context_none_without_dot():
    assert C.parse_dot_context("let n := 3", 10) is None


def test_literal_base_type():
    assert C.literal_base_type("1") == "Int"
    assert C.literal_base_type("1.5") == "Float"
    assert C.literal_base_type('"hi"') == "String"
    assert C.literal_base_type("true") == "Bool"
    assert C.literal_base_type("n") is None


def test_format_type_normalises_refinement_binder():
    # The internal binder (e.g. v⁴⁴) is normalised to ν and trivial refinements
    # are dropped.
    _, index, _ = analyse("def main (u:Int) : Int :=\n    let x := 7 in\n    x;\n")
    r = index.type_at(1, col_after("def main (u:Int) : Int :=\n    let x := 7 in\n    x;\n", 1, "7") - 1)
    assert r is not None
    s = C.format_type(r[0])
    assert s.startswith("{ν:Int |") and "= 7" in s


# --------------------------------------------------------------------------- #
# Type index keystone
# --------------------------------------------------------------------------- #


def test_type_index_recovers_refined_literal_type():
    src = "def main (u:Int) : Int :=\n    let x := 41 in\n    x;\n"
    _, index, errs = analyse(src)
    assert errs == []
    # cursor on the '1' of '41' (line 1, the literal starts after 'let x = ')
    c = src.splitlines()[1].index("41")
    r = index.type_at(1, c)
    assert r is not None
    assert "41" in str(r[0])


def test_type_index_includes_locals_in_scope():
    src = "def main (u:Int) : Int :=\n    let x := 41 in\n    x;\n"
    _, index, _ = analyse(src)
    c = src.splitlines()[2].index("x")
    scope = index.scope_at(2, c)
    assert scope is not None
    assert any(n.name == "x" for n, _ in scope.vars())


# --------------------------------------------------------------------------- #
# Tier 1 & 2 completion
# --------------------------------------------------------------------------- #

METHODS_SRC = (
    'def Int.toString (n:Int) : String := native "str(n)";\n'
    "def Int.double (n:Int) : Int := n + n;\n"
    "def main (u:Int) : Int :=\n"
    "    let n := 4 in\n"
    "    n.double;\n"
)


def test_tier1_literal_receiver_lists_methods():
    d, index, errs = analyse(METHODS_SRC)
    assert errs == []
    # Probe inside main's body where the Int methods are in scope: replace the
    # receiver position with a literal dot. Use the real 'n.double' line.
    line0 = 4
    col = col_after(METHODS_SRC, line0, "n.")
    comps = C.compute_completions(METHODS_SRC, line0, col, d.typing_ctx, index)
    assert "double" in labels(comps)
    assert "toString" in labels(comps)


def test_tier2_variable_receiver_post_receiver_signature():
    d, index, _ = analyse(METHODS_SRC)
    line0 = 4
    col = col_after(METHODS_SRC, line0, "n.")
    comps = C.compute_completions(METHODS_SRC, line0, col, d.typing_ctx, index)
    double = by_label(comps, "double")
    # `Int.double : Int -> Int`; after the receiver is consumed, nothing remains
    # but the return type.
    assert double.detail == "Int"


def test_identifier_completion_without_dot():
    d, index, _ = analyse(METHODS_SRC)
    line0 = 4
    # cursor right after 'n' (no dot) -> identifier completion includes 'n'
    col = col_after(METHODS_SRC, line0, "    n")
    comps = C.compute_completions(METHODS_SRC, line0, col - 1, d.typing_ctx, index)
    assert "n" in labels(comps)


# --------------------------------------------------------------------------- #
# Tier 3: refinement-aware feasibility
# --------------------------------------------------------------------------- #

REFINED_SRC = (
    "def Int.half (x:{v:Int | v % 2 = 0}) : Int := x / 2;\n"
    "def main (u:Int) : Int :=\n"
    "    let a : {v:Int | v = 4} := 4 in\n"
    "    let b : {v:Int | v = 5} := 5 in\n"
    "    a.half;\n"
)


def _half_for_receiver(varname):
    d, index, _ = analyse(REFINED_SRC)
    line0 = 4
    col = col_after(REFINED_SRC, line0, "a.")
    scope = index.scope_at(line0, col)
    scope_vars = scope.vars()
    from aeon.lsp.typeindex import TypeObservation
    from aeon.utils.location import SynthesizedLocation

    ty = next(t for n, t in scope_vars if n.name == varname)
    obs = TypeObservation(SynthesizedLocation("x"), scope, ty)
    comps = C.method_completions("Int", scope_vars, receiver_obs=obs, enable_feasibility=True)
    return by_label(comps, "half")


def test_tier3_even_receiver_is_feasible():
    half = _half_for_receiver("a")  # a == 4, even
    assert half.feasible is True
    assert half.sort_text.startswith("0")
    assert "satisfies" in half.documentation


def test_tier3_odd_receiver_is_infeasible():
    half = _half_for_receiver("b")  # b == 5, odd -> violates v % 2 == 0
    assert half.feasible is False
    assert half.sort_text.startswith("1")  # de-ranked below feasible methods
    assert "precondition" in half.documentation


def test_tier3_receiver_satisfies_decides_subtyping():
    from aeon.core.liquid import LiquidApp, LiquidLiteralInt, LiquidVar
    from aeon.core.types import RefinedType, t_int
    from aeon.typechecking.context import TypingContext
    from aeon.utils.location import SynthesizedLocation
    from aeon.utils.name import Name

    def eq(n, val):
        v = Name(n, 1)
        return RefinedType(v, t_int, LiquidApp(Name("==", 0), [LiquidVar(v), LiquidLiteralInt(val)]))

    def even(n):
        v = Name(n, 1)
        ref = LiquidApp(
            Name("==", 0),
            [LiquidApp(Name("%", 0), [LiquidVar(v), LiquidLiteralInt(2)]), LiquidLiteralInt(0)],
        )
        return RefinedType(v, t_int, ref)

    ctx = TypingContext()
    loc = SynthesizedLocation("t")
    assert C.receiver_satisfies(ctx, eq("a", 4), even("x"), loc) is True
    assert C.receiver_satisfies(ctx, eq("b", 5), even("x"), loc) is False


# --------------------------------------------------------------------------- #
# Navigation: symbols, definition, inlay hints
# --------------------------------------------------------------------------- #

NAV_SRC = (
    "def inc (n:Int) : Int := n + 1;\ndef main (u:Int) : Int :=\n    let x := 41 in\n    let y := inc x in\n    y;\n"
)


def test_document_symbols_lists_top_level_defs():
    d, _, _ = analyse(NAV_SRC)
    syms = N.document_symbols(d.core, NAV_SRC)
    names = [s.name for s in syms]
    assert names == ["inc", "main"]
    assert all(s.is_function for s in syms)


def test_go_to_definition_resolves_function_use():
    d, _, _ = analyse(NAV_SRC)
    di = N.build_def_index(d.core, NAV_SRC)
    # 'inc' used on line 3 (0-indexed) "    let y = inc x in"
    col = NAV_SRC.splitlines()[3].index("inc") + 1
    span = di.definition_at(3, col)
    assert span is not None
    assert span[0] == 1  # defined on source line 1 (1-indexed)


def test_go_to_definition_resolves_let_binding():
    d, _, _ = analyse(NAV_SRC)
    di = N.build_def_index(d.core, NAV_SRC)
    # 'x' used in 'inc x' on line 3
    col = NAV_SRC.splitlines()[3].rindex("x")
    span = di.definition_at(3, col)
    assert span is not None
    assert span[0] == 3  # 'let x' on source line 3 (1-indexed)


def test_inlay_hints_show_inferred_refinement():
    d, index, _ = analyse(NAV_SRC)
    hints = N.inlay_hints(d.core, NAV_SRC, index)
    by_line = {h.line: h.label for h in hints}
    # `let x = 41` -> inferred refined Int singleton
    assert 3 in by_line
    assert "Int" in by_line[3] and "41" in by_line[3]
    # `let y = inc x` -> Int
    assert 4 in by_line
    assert "Int" in by_line[4]


# --------------------------------------------------------------------------- #
# Driver: core/context retained even when type checking fails
# --------------------------------------------------------------------------- #


def test_core_retained_on_type_error():
    # Ill-typed: assigning 5 to {v:Int | v == 4}. Type checking fails, but the
    # program elaborates, so tooling state must still be available.
    src = "def main (u:Int) : Int :=\n    let a : {v:Int | v = 4} := 5 in\n    a;\n"
    d, index, errs = analyse(src)
    assert errs, "expected a type error"
    assert d.core is not None
    assert d.typing_ctx is not None
    assert index is not None


def test_core_cleared_on_parse_error():
    src = "def main (u:Int) : Int := !!! not valid"
    d, index, errs = analyse(src)
    assert errs
    assert d.core is None
    assert index is None


# --------------------------------------------------------------------------- #
# Adapter integration: parse populates the caches the server handlers read
# --------------------------------------------------------------------------- #


class _MockDocument:
    def __init__(self, source: str):
        self.source = source


class _MockWorkspace:
    def __init__(self, source: str):
        self._source = source

    def get_text_document(self, uri: str) -> _MockDocument:
        return _MockDocument(self._source)


class _MockLS:
    def __init__(self, source: str):
        cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=1)
        self.aeon_driver = AeonDriver(cfg)
        self.workspace = _MockWorkspace(source)


def test_adapter_parse_populates_type_index_and_drives_completion():
    import asyncio

    from aeon.lsp import aeon_adapter

    uri = "file:///integration.ae"
    ls = _MockLS(METHODS_SRC)
    asyncio.run(aeon_adapter.parse(ls, uri))

    index = aeon_adapter.get_type_index(uri)
    typing_ctx = aeon_adapter.get_typing_ctx(uri)
    assert index is not None and typing_ctx is not None

    col = col_after(METHODS_SRC, 4, "n.")
    comps = C.compute_completions(METHODS_SRC, 4, col, typing_ctx, index)
    assert "double" in labels(comps)


# --------------------------------------------------------------------------- #
# Decidability warnings surface as LSP Warning diagnostics (issue #438)
# --------------------------------------------------------------------------- #

_NONLINEAR_SRC = "def mul (x:Int) (y:Int) : {v:Int | v = x * y} := x * y;\ndef main (_:Int) : Unit := print 0;"
_LINEAR_SRC = "def f (x:Int) : {v:Int | v = x * 2} := x * 2;\ndef main (_:Int) : Unit := print 0;"


def test_adapter_emits_warning_diagnostic_for_nonlinear_refinement():
    import asyncio

    from lsprotocol.types import DiagnosticSeverity

    from aeon.lsp import aeon_adapter

    ls = _MockLS(_NONLINEAR_SRC)
    result = asyncio.run(aeon_adapter.parse(ls, "file:///nl_warn.ae"))

    warnings = [d for d in result.diagnostics if d.severity == DiagnosticSeverity.Warning]
    assert len(warnings) == 1
    assert "nonlinear multiplication" in warnings[0].message
    # 1-indexed core (1, 40) -> 0-indexed LSP (0, 39).
    assert warnings[0].range.start.line == 0


def test_adapter_no_warning_for_linear_refinement():
    import asyncio

    from lsprotocol.types import DiagnosticSeverity

    from aeon.lsp import aeon_adapter

    ls = _MockLS(_LINEAR_SRC)
    result = asyncio.run(aeon_adapter.parse(ls, "file:///lin_ok.ae"))

    assert [d for d in result.diagnostics if d.severity == DiagnosticSeverity.Warning] == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
