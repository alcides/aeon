from __future__ import annotations


from aeon.core.terms import Term, Application, Literal, Var
from aeon.core.types import top, BaseType
from aeon.frontend.anf_converter import ensure_anf
from aeon.logger.logger import setup_logger
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Definition
from aeon.synthesis_grammar.synthesizer import synthesize, gengy_default_config
from aeon.typechecking.typeinfer import check_type_errors

setup_logger()

synth_config = gengy_default_config
synth_config["timer_limit"] = 0.25


def test_fitness():

    code = """def year : Int = 2023;
        def synth (i: Int): Int { (?hole: Int) * i}
    """

    prog = parse_program(code)
    p, ctx, ectx, _ = desugar(prog)
    p = ensure_anf(p)
    check_type_errors(ctx, p, top)
    internal_minimize = Definition(
        name="__internal__minimize_int_synth_0",
        args=[],
        type=BaseType("Int"),
        body=Application(Application(Var("synth"), Literal(7, BaseType("Int"))), Application(Var("-"), Var("synth"))),
    )
    term, _ = synthesize(
        ctx, ectx, p, [("synth", ["hole"])], {"synth": {"minimize_int": [internal_minimize]}}, synth_config=synth_config
    )

    assert isinstance(term, Term)


def test_fitness2():
    code = """def year : Int = 2023;
            @minimize_int( year - synth(7) )
            def synth (i:Int) : Int {(?hole: Int) * i}
        """
    prog = parse_program(code)
    p, ctx, ectx, metadata = desugar(prog)
    p = ensure_anf(p)
    check_type_errors(ctx, p, top)
    term, _ = synthesize(ctx, ectx, p, [("synth", ["hole"])], metadata, synth_config=synth_config)

    assert isinstance(term, Term)
