"""String-literal escape handling in both parsers (sugar and core).

These tests assert that the parser decodes standard escape sequences (``\\n``,
``\\t``, ``\\\\``, ``\\"``) and Unicode escapes (``\\uXXXX``), and that raw UTF-8
characters in source survive unmangled.
"""

from aeon.sugar.parser import parse_expression
from aeon.sugar.program import SLiteral
from aeon.core.parser import parse_term
from aeon.core.terms import Literal


def _sugar(src: str) -> str:
    t = parse_expression(src)
    assert isinstance(t, SLiteral)
    assert isinstance(t.value, str)
    return t.value


def _core(src: str) -> str:
    t = parse_term(src)
    assert isinstance(t, Literal)
    assert isinstance(t.value, str)
    return t.value


# --- Sugar parser ---


def test_sugar_plain():
    assert _sugar('"hello"') == "hello"


def test_sugar_newline_escape():
    assert _sugar('"a\\nb"') == "a\nb"


def test_sugar_tab_escape():
    assert _sugar('"tab\\there"') == "tab\there"


def test_sugar_quote_escape():
    assert _sugar('"q\\"end"') == 'q"end'


def test_sugar_backslash_escape():
    assert _sugar('"back\\\\slash"') == "back\\slash"


def test_sugar_utf8_literal():
    assert _sugar('"unicode☃"') == "unicode☃"


def test_sugar_unicode_escape():
    assert _sugar('"snow\\u2603man"') == "snow☃man"


# --- Core parser ---


def test_core_plain():
    assert _core('"hello"') == "hello"


def test_core_newline_escape():
    assert _core('"a\\nb"') == "a\nb"


def test_core_tab_escape():
    assert _core('"tab\\there"') == "tab\there"


def test_core_quote_escape():
    assert _core('"q\\"end"') == 'q"end'


def test_core_backslash_escape():
    assert _core('"back\\\\slash"') == "back\\slash"


def test_core_utf8_literal():
    assert _core('"unicode☃"') == "unicode☃"


def test_core_unicode_escape():
    assert _core('"snow\\u2603man"') == "snow☃man"
