import pytest

from aeon.core.terms import Abstraction, Term, Var
from aeon.core.types import top, t_bool, t_int, t_float, t_string
from aeon.frontend.anf_converter import ensure_anf
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.synthesis_grammar.synthesizer import synthesize, gengy_default_config
from aeon.typechecking.typeinfer import check_type_errors


def synthesis_and_return(code):
    synth_config = gengy_default_config
    synth_config["timer_limit"] = 0.25

    hole_name = "hole"

    prog = parse_program(code)
    p, ctx, ectx, metadata = desugar(prog)
    p = ensure_anf(p)
    check_type_errors(ctx, p, top)
    _, holes = synthesize(ctx, ectx, p, [("synth", [hole_name])], metadata, synth_config=synth_config)
    return holes[hole_name], ctx


@pytest.mark.parametrize("ty", [t_bool, t_int, t_float, t_string])
def test_e2e_synthesis_basic_types(ty):

    code = f"""def synth : {ty} = ?hole;"""
    t, ctx = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert not check_type_errors(ctx, t, ty)


def test_e2e_synthesis_var():
    code = """type A; def a : A = native "1";  def synth : A = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert t == Var("a")


def test_e2e_synthesis_abs():
    code = """def synth : (x:Int) -> Bool = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Abstraction)
