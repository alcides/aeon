from aeon.core.terms import Term
from aeon.core.types import top

from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.identification import iterate_top_level
from aeon.typechecking.typeinfer import check_type_errors


def extract_core(source: str) -> Term:
    prog = parse_program(source)
    core, ctx, _ = desugar(prog)
    check_type_errors(ctx, core, top)
    return core


def test_hole_minimize_int():
    code = """
            def year : Int = 2023;
            def minus : (a:Int) -> (b:Int) -> Int = \\x -> \\y -> x - y;
            @minimize_int( year - (synth 7) )
            def synth(a: Int) : Int { (?hole:Int) * a}
        """
    core = extract_core(code)
    assert len(list(iterate_top_level(core))) == 3 + 1


def test_eq():
    aeon_code = """
        def main(args:Int) : Unit {
            x : String = "ola";
            x1 : String = x;
            x2 : String = x;
            z3 : Bool = x1 == x2;
            print z3
        }"""
    prog: Program = parse_program(aeon_code)
    (
        core_ast,
        typing_ctx,
        evaluation_ctx,
        metadata,
    ) = desugar(prog)

    type_errors = check_type_errors(typing_ctx, core_ast, top)
    for te in type_errors:
        print(te)
    assert len(type_errors) == 0
