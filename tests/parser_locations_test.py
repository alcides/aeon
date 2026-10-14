"""Inlining precedence rules must preserve diagnostic spans and grouping."""

import pytest

from aeon.sugar.parser import mk_parser
from aeon.sugar.program import SApplication, SVar
from aeon.utils.location import FileLocation


@pytest.mark.parametrize(
    "source,path,start,end",
    [
        ("(1 + 2) *\n  3", (), (1, 1), (2, 4)),
        ("(1 + 2) *\n  3", ("fun", "arg"), (1, 2), (1, 7)),
        ("(1 + 2) *\n  3", ("arg",), (2, 3), (2, 4)),
        ("f (g x)", ("arg",), (1, 4), (1, 7)),
        ("(1.plus 2).toString", ("arg",), (1, 2), (1, 10)),
        ("if true then\n  f (1 + 2) else 0", ("then", "arg"), (2, 6), (2, 11)),
    ],
)
def test_parenthesized_and_multiline_expression_spans(source, path, start, end):
    term = mk_parser("expression", filename="spans.ae")(source)
    for field in path:
        term = getattr(term, field)
    assert term.loc == FileLocation("spans.ae", start, end)


def test_precedence_and_associativity_after_inlining():
    parse = mk_parser("expression")

    def operator(term):
        assert isinstance(term, SApplication) and isinstance(term.fun, SApplication)
        assert isinstance(term.fun.fun, SVar)
        return term.fun.fun.name.name

    term = parse("1 + 2 * 3")
    assert operator(term) == "+"
    assert operator(term.arg) == "*"
    term = parse("8 - 3 - 1")
    assert operator(term) == "-"
    assert operator(term.fun.arg) == "-"
