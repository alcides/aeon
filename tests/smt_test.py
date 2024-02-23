from __future__ import annotations

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.terms import Term
from aeon.core.types import BaseType
from aeon.core.types import t_int
from aeon.core.types import top
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.typechecking.typeinfer import check_type_errors
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint


def extract_core(source: str) -> Term:
    prog = parse_program(source)
    core, ctx, _ = desugar(prog)
    core_anf = ensure_anf(core)
    check_type_errors(ctx, core_anf, top)
    return core_anf


example = Implication(
    "x",
    t_int,
    LiquidApp("==", [LiquidVar("x"), LiquidLiteralInt(3)]),
    LiquidConstraint(LiquidApp("==", [LiquidVar("x"), LiquidLiteralInt(3)])),
)


def test_smt_example3():
    assert smt_valid(example)


example2 = Implication(
    "x",
    BaseType("a"),
    LiquidLiteralBool(True),
    Implication(
        "y",
        BaseType("a"),
        LiquidApp("==", [LiquidVar("x"), LiquidVar("y")]),
        LiquidConstraint(LiquidApp("==", [LiquidVar("x"), LiquidVar("y")])),
    ),
)


def test_other_sorts():
    assert smt_valid(example2)


# this test fails with def List_new : {x:List | List_size(x) == 0} ,
# but with def List_new : {u:List | List_size(u) == 0} works fine
def test_uninterpreted():
    aeon_code = """
type List;
def List_size: (l:List) -> Int = uninterpreted;

def List_new : {x:List | List_size(x) == 0} = native "[]" ;

#def List_new : {u:List | List_size(u) == 0} = native "[]" ;

def List_append: (l:List) -> (i: Int) -> {l2:List | List_size(l2) == (List_size(l) + 1)} = native "lambda xs: lambda x: xs + [x]";

def main (x:Int) : Unit {
    empty = List_new;
    one = List_append empty 3;
    print(one)
}"""
    prog: Program = parse_program(aeon_code)
    (
        core_ast,
        typing_ctx,
        evaluation_ctx,
    ) = desugar(prog)

    core_ast_anf = ensure_anf(core_ast)
    type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
    assert len(type_errors) == 0
