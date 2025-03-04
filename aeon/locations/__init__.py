# TODO: Do this for all AST
from dataclasses import dataclass

from lark import Token


@dataclass
class SourcePosition:
    line_start: int
    line_end: int
    col_start: int
    col_ind: int

    @staticmethod
    def fromToken(t: Token):
        return SourcePosition(t.line, t.end_line, t.column, t.end_column)
