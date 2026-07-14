import pytest
from lsprotocol.types import CodeAction, CodeActionKind, Command, MessageType, Position, Range, ShowMessageParams

from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.lsp.aeon_adapter import HolePosition, ParseResult, find_holes_in_source
from aeon.lsp.server import SYNTHESIZERS, SYNTHESIZE_COMMAND, AeonLanguageServer, _run_synthesis
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SilentSynthesisUI

setup_logger()


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------


def make_driver() -> AeonDriver:
    cfg = AeonConfig(synthesizer="gp", synthesis_ui=SilentSynthesisUI(), synthesis_budget=5)
    return AeonDriver(cfg)


def make_range(sl: int, sc: int, el: int, ec: int) -> Range:
    return Range(start=Position(line=sl, character=sc), end=Position(line=el, character=ec))


class MockDocument:
    def __init__(self, source: str):
        self.source = source


class MockWorkspace:
    def __init__(self, source: str):
        self._source = source

    def get_text_document(self, uri: str) -> MockDocument:
        return MockDocument(self._source)


class MockProtocol:
    """Stand-in for pygls' LanguageServerProtocol: custom notifications are
    sent via ``protocol.notify(method, params)`` (NOT ``ls.send_notification``,
    which does not exist on the real server)."""

    def __init__(self) -> None:
        self.notifications: list[tuple[str, object]] = []

    def notify(self, method: str, params: object = None) -> None:
        self.notifications.append((method, params))


class MockLS:
    """Minimal stand-in for AeonLanguageServer used by _run_synthesis.

    Mirrors the real pygls API surface that the synthesis code relies on: a
    ``protocol.notify`` for custom notifications and ``window_show_message``."""

    def __init__(self, source: str):
        self.workspace = MockWorkspace(source)
        self.messages: list[tuple[str, MessageType]] = []
        self.protocol = MockProtocol()

    def window_show_message(self, params: ShowMessageParams) -> None:
        self.messages.append((params.message, params.type))


# ---------------------------------------------------------------------------
# find_holes_in_source
# ---------------------------------------------------------------------------


def test_find_holes_empty_source():
    assert find_holes_in_source("") == []


def test_find_holes_no_holes():
    assert find_holes_in_source("def x : Int := 42;") == []


def test_find_holes_single():
    source = "def x : Int := ?hole;"
    result = find_holes_in_source(source)
    assert len(result) == 1
    assert result[0].name == "hole"
    assert result[0].range.start.line == 0
    assert result[0].range.start.character == source.index("?")
    assert result[0].range.end.character == source.index("?") + len("?hole")


def test_find_holes_multiple_same_line():
    source = "?foo ?bar"
    result = find_holes_in_source(source)
    assert [h.name for h in result] == ["foo", "bar"]
    assert result[0].range.start.character == 0
    assert result[1].range.start.character == 5


def test_find_holes_multiple_lines():
    source = "def x : Int := ?foo;\ndef y : Bool := ?bar;"
    result = find_holes_in_source(source)
    assert len(result) == 2
    assert result[0].name == "foo"
    assert result[0].range.start.line == 0
    assert result[1].name == "bar"
    assert result[1].range.start.line == 1


def test_find_holes_at_line_start():
    source = "a\n?x\nb"
    result = find_holes_in_source(source)
    assert len(result) == 1
    assert result[0].range.start.line == 1  # 0-indexed: line 0="a", line 1="?x"
    assert result[0].range.start.character == 0
    assert result[0].range.end.character == 2


def test_find_holes_question_mark_only_not_matched():
    # A bare '?' with no following identifier should not match
    source = "? ="
    assert find_holes_in_source(source) == []


def test_find_holes_range_spans_full_token():
    source = "?longname"
    result = find_holes_in_source(source)
    assert len(result) == 1
    assert result[0].range.start.character == 0
    assert result[0].range.end.character == len("?longname")


# ---------------------------------------------------------------------------
# ParseResult.holes
# ---------------------------------------------------------------------------


def test_parse_result_default_holes_empty():
    pr = ParseResult(diagnostics=[])
    assert pr.holes == []


def test_parse_result_stores_holes():
    hole_range = make_range(0, 0, 0, 4)
    hp = HolePosition(name="foo", range=hole_range)
    pr = ParseResult(diagnostics=[], holes=[hp])
    assert len(pr.holes) == 1
    assert pr.holes[0].name == "foo"


# ---------------------------------------------------------------------------
# AeonLanguageServer._ranges_overlap
# ---------------------------------------------------------------------------


@pytest.fixture
def ls() -> AeonLanguageServer:
    return AeonLanguageServer(make_driver())


def test_ranges_overlap_identical(ls):
    r = make_range(0, 5, 0, 10)
    assert ls._ranges_overlap(r, r)


def test_ranges_overlap_partial(ls):
    r1 = make_range(0, 0, 0, 10)
    r2 = make_range(0, 5, 0, 15)
    assert ls._ranges_overlap(r1, r2)
    assert ls._ranges_overlap(r2, r1)


def test_ranges_adjacent_touch(ls):
    # With boundary-inclusive semantics a cursor exactly at the boundary triggers both
    r1 = make_range(0, 0, 0, 5)
    r2 = make_range(0, 5, 0, 10)
    assert ls._ranges_overlap(r1, r2)


def test_ranges_no_overlap_gap(ls):
    r1 = make_range(0, 0, 0, 5)
    r2 = make_range(0, 6, 0, 10)  # one-character gap
    assert not ls._ranges_overlap(r1, r2)


def test_ranges_no_overlap_different_lines(ls):
    r1 = make_range(0, 0, 0, 10)
    r2 = make_range(1, 0, 1, 10)
    assert not ls._ranges_overlap(r1, r2)


def test_ranges_overlap_cursor_inside(ls):
    hole = make_range(3, 14, 3, 19)
    cursor = make_range(3, 15, 3, 15)  # zero-width cursor inside hole
    assert ls._ranges_overlap(hole, cursor)


def test_ranges_overlap_cursor_at_hole_start(ls):
    hole = make_range(0, 4, 0, 9)
    cursor = make_range(0, 4, 0, 4)
    assert ls._ranges_overlap(hole, cursor)


# ---------------------------------------------------------------------------
# synthesizers list
# ---------------------------------------------------------------------------


def test_synthesizers_list_non_empty():
    assert len(SYNTHESIZERS) > 0


def test_synthesizers_includes_defaults():
    assert "tdsyn_enumerative" in SYNTHESIZERS
    assert "tdsyn_random" in SYNTHESIZERS
    assert "gp" in SYNTHESIZERS
    assert "enumerative" in SYNTHESIZERS
    assert "llm_qwen2.5-coder-32b" in SYNTHESIZERS
    assert "llm" not in SYNTHESIZERS


# ---------------------------------------------------------------------------
# _run_synthesis (integration)
# ---------------------------------------------------------------------------


def test_run_synthesis_basic_int():
    source = "def synth : Int := ?hole;"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", "gp")

    assert result is not None
    synthesized_str, hole_range = result
    assert isinstance(synthesized_str, str)
    assert len(synthesized_str) > 0
    assert hole_range.start.line == 0
    assert hole_range.start.character == source.index("?")
    # Live progress must reach the client via protocol.notify (regression: the
    # info view showed no progress because the UI called a nonexistent
    # ls.send_notification, swallowed by a bare except).
    progress = [p for m, p in mock_ls.protocol.notifications if m == "aeon/synthesisProgress"]
    assert progress, "no aeon/synthesisProgress notifications were emitted"
    # The final update fills the bar to 100% (elapsed == budget) and is marked done.
    final = progress[-1]
    assert final["done"] is True
    assert final["algorithm"]
    assert final["budget"] > 0 and final["elapsed"] == final["budget"]


def test_run_synthesis_returns_none_on_parse_error():
    source = "this is not valid aeon !!!"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", "gp")

    assert result is None
    # Either a parse exception or returned errors should produce an error message
    assert any(t == MessageType.Error for _, t in mock_ls.messages)


def test_run_synthesis_returns_none_when_hole_missing():
    source = "def x : Int := 42;"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "missing", "gp")

    assert result is None


def test_run_synthesis_unknown_synthesizer():
    source = "def synth : Int := ?hole;"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", "does_not_exist")

    assert result is None
    assert any("synthesizer" in msg.lower() or "unknown" in msg.lower() for msg, _ in mock_ls.messages)


# ---------------------------------------------------------------------------
# code_action: one action per synthesizer
# ---------------------------------------------------------------------------


def _build_code_actions(hole: HolePosition, uri: str) -> list[CodeAction]:
    """Mirrors the action-building loop inside the code_action handler."""
    from aeon.synthesis.modules.synthesizerfactory import synthesizer_label

    actions = []
    for synthesizer in SYNTHESIZERS:
        label = synthesizer_label(synthesizer)
        action = CodeAction(
            title=f"Synthesize ?{hole.name} with {label}",
            kind=CodeActionKind.RefactorRewrite,
            command=Command(
                title=f"Synthesize ?{hole.name} with {label}",
                command=SYNTHESIZE_COMMAND,
                arguments=[uri, hole.name, synthesizer],
            ),
        )
        actions.append(action)
    return actions


def test_code_action_creates_one_action_per_synthesizer():
    hole = HolePosition(name="hole", range=make_range(0, 14, 0, 19))
    actions = _build_code_actions(hole, "file:///test.ae")

    assert len(actions) == len(SYNTHESIZERS)


def test_code_action_titles_use_readable_labels():
    from aeon.synthesis.modules.synthesizerfactory import synthesizer_label

    hole = HolePosition(name="hole", range=make_range(0, 14, 0, 19))
    actions = _build_code_actions(hole, "file:///test.ae")

    titles = [a.title for a in actions]
    for synthesizer in SYNTHESIZERS:
        # The menu shows the human-readable label, not the internal id.
        assert any(synthesizer_label(synthesizer) in t for t in titles)


def test_code_action_commands_have_correct_arguments():
    uri = "file:///test.ae"
    hole = HolePosition(name="myhole", range=make_range(1, 4, 1, 11))
    actions = _build_code_actions(hole, uri)

    for action, synthesizer in zip(actions, SYNTHESIZERS):
        args = action.command.arguments
        assert args[0] == uri
        assert args[1] == "myhole"
        assert args[2] == synthesizer


# ---------------------------------------------------------------------------
# _run_synthesis parametrized over all synthesizers
# ---------------------------------------------------------------------------


class _FakeOllamaResponse:
    response = ""


@pytest.mark.parametrize("synthesizer", SYNTHESIZERS)
def test_run_synthesis_each_synthesizer(synthesizer, monkeypatch):
    source = "def synth : Int := ?hole;"
    mock_ls = MockLS(source)
    driver = make_driver()

    if synthesizer.startswith("llm"):
        monkeypatch.setattr("aeon.synthesis.modules.llm.prepare_ollama_model", lambda _model: None)
        monkeypatch.setattr("aeon.synthesis.modules.llm.release_ollama_model", lambda _model: None)
        monkeypatch.setattr("ollama.generate", lambda **kwargs: _FakeOllamaResponse())
        result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", synthesizer)
        # With a blank response the LLM synthesizer cannot find a valid term;
        # we only verify it completes without raising an exception.
        assert result is None or isinstance(result, tuple)
        return

    # These backends need a spec the plain ``Int`` hole does not provide:
    # decision_tree needs @csv_data/@example rows; symetric needs a @minimize
    # objective; sygus needs an SMT-expressible constraint. They legitimately
    # produce no term here — just verify they complete without raising.
    if synthesizer in ("decision_tree", "sygus", "symetric"):
        result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", synthesizer)
        assert result is None or isinstance(result, tuple)
        return

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", synthesizer)

    assert result is not None, f"Synthesizer '{synthesizer}' returned None. Messages: {mock_ls.messages}"
    synthesized_str, hole_range = result
    assert isinstance(synthesized_str, str) and len(synthesized_str) > 0
    assert hole_range.start.line == 0
    assert hole_range.start.character == source.index("?")


# ---------------------------------------------------------------------------
# Parse diagnostics for invalid source
# ---------------------------------------------------------------------------


def test_parse_syntax_error_returns_diagnostic():
    import asyncio
    import io

    from aeon.lsp.aeon_adapter import _parse
    from lsprotocol.types import DiagnosticSeverity

    driver = make_driver()
    result = asyncio.run(_parse(io.StringIO("this is not valid aeon !!!"), driver, "file:///test.ae"))

    assert len(result.diagnostics) == 1
    assert result.diagnostics[0].severity == DiagnosticSeverity.Error
    assert "Unexpected" in result.diagnostics[0].message


def test_parse_unexpected_characters_returns_syntax_diagnostic():
    import asyncio
    import io

    from aeon.lsp.aeon_adapter import _parse
    from lsprotocol.types import DiagnosticSeverity

    driver = make_driver()
    result = asyncio.run(_parse(io.StringIO('def x : Int := "unclosed'), driver, "file:///test.ae"))

    assert len(result.diagnostics) == 1
    assert result.diagnostics[0].severity == DiagnosticSeverity.Error
    assert "Unknown exception" not in result.diagnostics[0].message
    assert "Unexpected character" in result.diagnostics[0].message


def test_parse_incomplete_definition_returns_diagnostic():
    import asyncio
    import io

    from aeon.lsp.aeon_adapter import _parse
    from lsprotocol.types import DiagnosticSeverity

    driver = make_driver()
    result = asyncio.run(_parse(io.StringIO("def x : Int :="), driver, "file:///test.ae"))

    assert len(result.diagnostics) == 1
    assert result.diagnostics[0].severity == DiagnosticSeverity.Error


def test_parse_missing_document_returns_diagnostic():
    import asyncio

    from aeon.lsp.aeon_adapter import parse
    from lsprotocol.types import DiagnosticSeverity

    class MissingDocWorkspace:
        def get_text_document(self, uri):
            raise KeyError("Document not found")

    class MissingDocLS:
        aeon_driver = make_driver()
        workspace = MissingDocWorkspace()

    result = asyncio.run(parse(MissingDocLS(), "file:///missing.ae"))

    assert len(result.diagnostics) == 1
    assert result.diagnostics[0].severity == DiagnosticSeverity.Error
    assert "Could not read document" in result.diagnostics[0].message


# ---------------------------------------------------------------------------
# Z3 verification errors
# ---------------------------------------------------------------------------


def test_z3_exception_message_decodes_bytes():
    from z3.z3types import Z3Exception

    from aeon.lsp.z3_errors import z3_diagnostic_message, z3_exception_message

    exc = Z3Exception(b"ast is not an expression")
    assert z3_exception_message(exc) == "ast is not an expression"
    assert z3_diagnostic_message(exc) == "Z3 verification error: ast is not an expression"


def test_parse_z3_exception_keeps_cached_holes(monkeypatch):
    import asyncio
    import io

    from z3.z3types import Z3Exception

    from aeon.lsp import aeon_adapter
    from aeon.lsp.aeon_adapter import _parse
    from lsprotocol.types import DiagnosticSeverity

    uri = "file:///z3_test.ae"
    source = "def synth : Int := ?hole;"
    driver = make_driver()
    driver.parse(filename=uri, aeon_code=source)
    aeon_adapter.cache_driver_analysis(driver, uri)

    def boom(*_args, **_kwargs):
        raise Z3Exception(b"ast is not an expression")

    monkeypatch.setattr(driver, "parse", boom)

    result = asyncio.run(_parse(io.StringIO(source), driver, uri))

    assert len(result.holes) == 1
    assert result.holes[0].name == "hole"
    assert any(
        d.severity == DiagnosticSeverity.Warning and "Z3 verification error" in d.message for d in result.diagnostics
    )


def test_run_synthesis_recovers_from_z3_with_cached_parse(monkeypatch):
    from z3.z3types import Z3Exception

    from aeon.lsp import aeon_adapter

    source = """
    @example(double 3 = 6)
    @example(double 4 = 8)
    def double (n:Int) : Int := ?hole;
    """
    uri = "file:///z3_synth.ae"
    mock_ls = MockLS(source)
    driver = make_driver()
    driver.parse(filename=uri, aeon_code=source)
    aeon_adapter.cache_driver_analysis(driver, uri)

    real_parse = driver.parse

    def parse_then_z3(*args, **kwargs):
        real_parse(*args, **kwargs)
        raise Z3Exception(b"ast is not an expression")

    monkeypatch.setattr(driver, "parse", parse_then_z3)

    result = _run_synthesis(driver, mock_ls, uri, "hole", "smt", budget_seconds=10)

    assert result is not None
    synthesized_str, _hole_range = result
    assert "n" in synthesized_str
    warning_msgs = [msg for msg, typ in mock_ls.messages if typ == MessageType.Warning]
    assert any("Z3 verification error" in msg for msg in warning_msgs)
    assert not any("parse failed" in msg for msg, _ in mock_ls.messages)
