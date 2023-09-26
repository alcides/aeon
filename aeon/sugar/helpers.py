from lark import Token
from aeon.core.terms import SourceLocation
from aeon.sugar.program import Node


def extract_boundary(el, start=True) -> tuple[int, int]:
    """Returns the start line/col or the end line/col pair, based on whether start is true or not."""
    match el:
        case [_]:
            assert el
            if start:
                return extract_boundary(el[0], start)
            else:
                return extract_boundary(el[-1], start)
        case Token(_):
            if start:
                return (el.line, el.start_pos)
            else:
                return (el.end_line, el.end_pos)
        case Node(_):
            if start:
                return (el.source_location.start_line, el.source_location.start_col)
            else:
                return (el.source_location.end_line, el.source_location.end_col)
        case _:
            assert False


def extract_position(*args) -> SourceLocation:
    "Position of a sequence of Nodes or Tokens"
    assert args
    (start_line, start_col) = extract_boundary(args[0], start=True)
    (end_line, end_col) = extract_boundary(args[-1], start=False)
    return SourceLocation(
        filename="@main", start_line=start_line, start_col=start_col, end_line=end_line, end_col=end_col
    )
