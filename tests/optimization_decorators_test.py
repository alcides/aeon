from aeon.core.terms import Term
from aeon.core.types import top
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.identification import iterate_top_level
from aeon.typechecking.typeinfer import check_type_errors


def extract_core(source: str) -> Term:
    prog = parse_program(source)
    core, ctx, _, _ = desugar(prog)
    core_anf = ensure_anf(core)
    check_type_errors(ctx, core_anf, top)
    return core_anf


def test_hole_minimize_int():
    code = """
            def year : Int = 2023;
            def minus : (a:Int) -> (b:Int) -> Int = \\x -> \\y -> x - y;
            @minimize_int( year - (synth 7) )
            def synth(a: Int) : Int { (?hole:Int) * a}
        """
    core = extract_core(code)
    assert len(list(iterate_top_level(core))) == 3 + 1


def test_eq() -> None:
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

    core_ast_anf = ensure_anf(core_ast)
    type_errors = check_type_errors(typing_ctx, core_ast_anf, top)
    assert len(type_errors) == 0
