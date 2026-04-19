from aeon.core.parser import parse_type
from aeon.core.terms import Annotation, Hole, Term, Var
from aeon.core.types import t_int
from aeon.synthesis.identification import get_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.holes import collect_hole_judgments, list_hole_infos
from aeon.synthesis.tactics.random_synth import TacticRandomSynthesizer
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.tactics.subtyping import fits
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("test")


def test_fits_int_refines_to_int():
    ctx = TypingContext()
    subt = parse_type(r"{k:Int | k > 0}")
    assert fits(ctx, subt, t_int)


def test_apply_question_uses_subtyping():
    y = Name("y", 0)
    yty = parse_type(r"{v:Int | v > 0}")
    ctx = TypingContext([VariableBinder(y, yty)])
    h = Name("h", 0)
    term = Annotation(Hole(h), t_int, loc=_loc)
    st = TacticState(ctx, term, t_int)
    out = tactic_apply_question(st, h)
    assert out is not None
    assert not get_holes(out.term)
    assert check_type(ctx, out.term, t_int)
    assert _strip_trivial_ascription(out.term) == Var(y, _loc)


def _strip_trivial_ascription(t: Term) -> Term:
    match t:
        case Annotation(expr=e, type=_):
            return e
        case _:
            return t


def test_constructor_builds_application_spine():
    f = Name("f", 0)
    fty = parse_type("(x:Int) -> Int")
    ctx = TypingContext([VariableBinder(f, fty)])
    r = Name("r", 0)
    term = Annotation(Hole(r), t_int, loc=_loc)
    st = TacticState(ctx, term, t_int)
    out = tactic_constructor(st, r)
    assert out is not None
    hs = get_holes(out.term)
    assert len(hs) == 1


def test_constructor_arrow_intro():
    ctx = TypingContext()
    h = Name("h", 0)
    goal = parse_type("(a:Int) -> Int")
    term = Annotation(Hole(h), goal, loc=_loc)
    st = TacticState(ctx, term, goal)
    out = tactic_constructor(st, h)
    assert out is not None
    assert len(get_holes(out.term)) == 1


def test_collect_hole_judgments_finds_arg_hole_type():
    f = Name("f", 0)
    fty = parse_type("(x:Int) -> Int")
    ctx = TypingContext([VariableBinder(f, fty)])
    r = Name("r", 0)
    term = Annotation(Hole(r), t_int, loc=_loc)
    out = tactic_constructor(TacticState(ctx, term, t_int), r)
    assert out is not None
    mp = collect_hole_judgments(out.ctx, out.term, t_int, refined_types=True)
    assert len(mp) == 1
    arg_ty, _ = next(iter(mp.values()))
    assert arg_ty == t_int


def test_list_hole_infos_includes_refinement_metadata():
    ctx = TypingContext()
    h = Name("h", 0)
    gty = parse_type(r"{z:Int | z > 1}")
    term = Annotation(Hole(h), gty, loc=_loc)
    infos = list_hole_infos(ctx, term, gty, refined_types=True)
    assert len(infos) == 1
    assert infos[0].refinement_predicate is not None


def test_tactic_random_synthesizer_smoke():
    x = Name("x", 0)
    ctx = TypingContext([VariableBinder(x, t_int)])
    syn = TacticRandomSynthesizer(seed=42)

    def validate(t) -> bool:
        return check_type(ctx, t, t_int)

    def evaluate(t):
        return [0.0]

    got = syn.synthesize(
        ctx=ctx,
        type=t_int,
        validate=validate,
        evaluate=evaluate,
        fun_name=Name("main", 0),
        metadata={},
        budget=2.0,
    )
    assert got is not None
    assert check_type(ctx, got, t_int)


def test_make_synthesizer_tactics():
    s = make_synthesizer("tactics")
    assert isinstance(s, TacticRandomSynthesizer)
