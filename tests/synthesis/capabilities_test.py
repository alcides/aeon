import pytest

from aeon.core.terms import Abstraction, Application, Literal, Term, Var
from aeon.core.types import top, t_bool, t_int, t_float, t_string
from aeon.synthesis_grammar.synthesizer import synthesize, gengy_default_config
from aeon.typechecking.typeinfer import check_type
from tests.driver import check_and_return_core


def synthesis_and_return(code):
    synth_config = gengy_default_config
    synth_config["timer_limit"] = 0.25

    hole_name = "hole"

    term, ctx, ectx, metadata = check_and_return_core(code)
    assert check_type(ctx, term, top)

    _, holes = synthesize(ctx,
                          ectx,
                          term, [("synth", [hole_name])],
                          metadata,
                          synth_config=synth_config,
                          refined_grammar=True)
    return holes[hole_name], ctx


@pytest.mark.parametrize("ty", [t_bool, t_int, t_float, t_string])
def test_e2e_synthesis_basic_types(ty):

    code = f"""def synth : {ty} = ?hole;"""
    t, ctx = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert check_type(ctx, t, ty)


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


def test_e2e_synthesis_app():
    code = """type A; def f : (x:Int) -> A = \\x -> native "1";  def synth : A = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Application)
    assert t.fun == Var("f")


def test_e2e_synthesis_ref():
    code = """def synth : {x:Int | x == 3} = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Literal)
    assert t.value == 3


def test_e2e_synthesis_ref2():
    code = """def synth : {x:Int | x > 3} = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Literal)
    assert t.value > 3


def test_e2e_synthesis_ref3():
    code = """def synth : {x:Int | x > 3 && x < 10} = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Literal)
    assert t.value > 3 and t.value < 10


def test_e2e_synthesis_ref4():
    code = """def synth : {x:Int | (x > 3 && x < 10) || (x > 20 && x < 30)} = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Literal)
    assert (t.value > 3 and t.value < 10) or (t.value > 20 and t.value < 30)


def test_e2e_synthesis_ref5():
    code = """def synth : {x:Float | x > 3 && x < 10} = ?hole;"""
    t, _ = synthesis_and_return(code)

    assert isinstance(t, Term)
    assert isinstance(t, Literal)
    assert t.value > 3 and t.value < 10


# TODO: tapps e tabs

# alpha equivalence
