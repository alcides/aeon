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


class MockLS:
    """Minimal stand-in for AeonLanguageServer used by _run_synthesis."""

    def __init__(self, source: str):
        self.workspace = MockWorkspace(source)
        self.messages: list[tuple[str, MessageType]] = []

    def window_show_message(self, params: ShowMessageParams) -> None:
        self.messages.append((params.message, params.type))


# ---------------------------------------------------------------------------
# find_holes_in_source
# ---------------------------------------------------------------------------


def test_find_holes_empty_source():
    assert find_holes_in_source("") == []


def test_find_holes_no_holes():
    assert find_holes_in_source("def x : Int = 42;") == []


def test_find_holes_single():
    source = "def x : Int = ?hole;"
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
    source = "def x : Int = ?foo;\ndef y : Bool = ?bar;"
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
    assert "gp" in SYNTHESIZERS
    assert "enumerative" in SYNTHESIZERS


# ---------------------------------------------------------------------------
# _run_synthesis (integration)
# ---------------------------------------------------------------------------


def test_run_synthesis_basic_int():
    source = "def synth : Int = ?hole;"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", "gp")

    assert result is not None
    synthesized_str, hole_range = result
    assert isinstance(synthesized_str, str)
    assert len(synthesized_str) > 0
    assert hole_range.start.line == 0
    assert hole_range.start.character == source.index("?")


def test_run_synthesis_returns_none_on_parse_error():
    source = "this is not valid aeon !!!"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", "gp")

    assert result is None
    # Either a parse exception or returned errors should produce an error message
    assert any(t == MessageType.Error for _, t in mock_ls.messages)


def test_run_synthesis_returns_none_when_hole_missing():
    source = "def x : Int = 42;"
    mock_ls = MockLS(source)
    driver = make_driver()

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "missing", "gp")

    assert result is None


def test_run_synthesis_unknown_synthesizer():
    source = "def synth : Int = ?hole;"
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
    actions = []
    for synthesizer in SYNTHESIZERS:
        action = CodeAction(
            title=f"Synthesize ?{hole.name} with {synthesizer}",
            kind=CodeActionKind.RefactorRewrite,
            command=Command(
                title=f"Synthesize ?{hole.name} with {synthesizer}",
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


def test_code_action_titles_contain_synthesizer_names():
    hole = HolePosition(name="hole", range=make_range(0, 14, 0, 19))
    actions = _build_code_actions(hole, "file:///test.ae")

    titles = [a.title for a in actions]
    for synthesizer in SYNTHESIZERS:
        assert any(synthesizer in t for t in titles)


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
    source = "def synth : Int = ?hole;"
    mock_ls = MockLS(source)
    driver = make_driver()

    if synthesizer == "llm":
        monkeypatch.setattr("ollama.generate", lambda **kwargs: _FakeOllamaResponse())
        result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", synthesizer)
        # With a blank response the LLM synthesizer cannot find a valid term;
        # we only verify it completes without raising an exception.
        assert result is None or isinstance(result, tuple)
        return

    if synthesizer == "decision_tree":
        result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", synthesizer)
        # decision_tree requires @csv_data training examples; without them it
        # cannot synthesize a plain hole — just verify it doesn't raise.
        assert result is None or isinstance(result, tuple)
        return

    result = _run_synthesis(driver, mock_ls, "file:///test.ae", "hole", synthesizer)

    assert result is not None, f"Synthesizer '{synthesizer}' returned None. Messages: {mock_ls.messages}"
    synthesized_str, hole_range = result
    assert isinstance(synthesized_str, str) and len(synthesized_str) > 0
    assert hole_range.start.line == 0
    assert hole_range.start.character == source.index("?")
