from __future__ import annotations

from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program


def test_match_lowering_intlist():
    # This test checks that Lean-style match syntax on an inductive
    # lowers to the generated `<Inductive>_rec` eliminator.
    #
    # Runtime / typechecking might require external deps; we focus on AST lowering.
    src = """
        inductive IntList
        | empty : IntList
        | cons (hd:Int) (tl:IntList) : IntList
        def mk (l:IntList) : IntList {
            match l with
            | empty => l
            | cons hd tl => l
        }
        def main (args:Int) : Int {
            0
        }
    """

    prog = parse_program(src)
    desugared = desugar(prog, is_main_hole=True)
    # Lowering should remove SMatch nodes and use the generated eliminator.
    dumped = str(desugared.program)
    # Our surface AST pretty-print includes "match ... with" for SMatch.
    assert "SMatch" not in dumped
    assert "IntList_rec" in dumped
