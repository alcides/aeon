from aeon.core.parser import parse_type
from aeon.core.terms import Annotation, Hole, If, Literal, Term, Var
from aeon.core.types import t_bool, t_int
from aeon.elaboration.context import build_typing_context
from aeon.prelude.prelude import typing_vars
from aeon.sugar.lowering import lower_to_core_context
from aeon.synthesis.identification import get_holes
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.synthesis.tactics.builtin import tactic_apply_question, tactic_constructor
from aeon.synthesis.tactics.assumption import tactic_assumption
from aeon.synthesis.tactics.by_cases import tactic_by_cases
from aeon.synthesis.tactics.split import tactic_split
from aeon.synthesis.tactics.choose_literal import tactic_choose_literal
from aeon.synthesis.tactics.holes import collect_hole_judgments, list_hole_infos
from aeon.synthesis.tactics.random_synth import TacticRandomSynthesizer
from aeon.synthesis.tactics.state import TacticState
from aeon.synthesis.tactics.subtyping import fits
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("test")


def _prelude_ctx() -> TypingContext:
    return lower_to_core_context(build_typing_context(typing_vars))


def test_fits_int_refines_to_int():
    ctx = TypingContext()
    subt = parse_type(r"{k:Int | k > 0}")
    assert fits(ctx, subt, t_int)


def test_assumption_succeeds_when_types_are_bidirectionally_subtyping():
    x = Name("x", 0)
    ty = parse_type(r"{v:Int | v > 0}")
    ctx = _prelude_ctx().with_var(x, ty)
    h = Name("h", 0)
    term = Annotation(Hole(h), ty, loc=_loc)
    st = TacticState(ctx, term, ty)
    out = tactic_assumption(st, h)
    assert out is not None
    assert not get_holes(out.term)
    assert check_type(ctx, out.term, ty)


def test_assumption_fails_when_only_forward_subtyping():
    """``apply?`` can use a stronger hypothesis at a looser goal; ``assumption`` cannot."""
    x = Name("x", 0)
    xty = parse_type(r"{v:Int | v > 5}")
    goal_ty = parse_type(r"{w:Int | w > 0}")
    ctx = _prelude_ctx().with_var(x, xty)
    h = Name("h", 0)
    term = Annotation(Hole(h), goal_ty, loc=_loc)
    st = TacticState(ctx, term, goal_ty)
    assert tactic_assumption(st, h) is None
    assert tactic_apply_question(st, h) is not None


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


def test_choose_literal_plain_int_defaults():
    ctx = TypingContext()
    h = Name("h", 0)
    term = Annotation(Hole(h), t_int, loc=_loc)
    st = TacticState(ctx, term, t_int)
    out = tactic_choose_literal(st, h)
    assert out is not None
    assert not get_holes(out.term)
    e = _strip_trivial_ascription(out.term)
    assert isinstance(e, Literal)
    assert e.value == 0
    assert check_type(ctx, out.term, t_int)


def test_choose_literal_refined_int_satisfies_predicate():
    ctx = _prelude_ctx()
    h = Name("h", 0)
    gty = parse_type(r"{z:Int | z > 2}")
    term = Annotation(Hole(h), gty, loc=_loc)
    st = TacticState(ctx, term, gty)
    out = tactic_choose_literal(st, h)
    assert out is not None
    e = _strip_trivial_ascription(out.term)
    assert isinstance(e, Literal)
    assert isinstance(e.value, int)
    assert e.value > 2
    assert check_type(ctx, out.term, gty)


def test_split_peels_conjunction_refinement():
    ctx = _prelude_ctx()
    h = Name("h", 0)
    full_ty = parse_type(r"{z:Int | z > 0 && z < 10}")
    term = Annotation(Hole(h), full_ty, loc=_loc)
    st = TacticState(ctx, term, full_ty)
    out = tactic_split(st, h)
    assert out is not None
    assert out.goal == full_ty
    mp = collect_hole_judgments(out.ctx, out.term, full_ty, refined_types=True)
    inner_ty, _ = mp[h]
    assert "&&" not in str(inner_ty)


def test_split_noop_without_conjunction():
    ctx = _prelude_ctx()
    h = Name("h", 0)
    term = Annotation(Hole(h), t_int, loc=_loc)
    st = TacticState(ctx, term, t_int)
    assert tactic_split(st, h) is None


def test_by_cases_splits_on_bool_hypothesis():
    b = Name("b", 0)
    ctx = _prelude_ctx().with_var(b, t_bool)
    h = Name("h", 0)
    term = Annotation(Hole(h), t_int, loc=_loc)
    st = TacticState(ctx, term, t_int)
    out = tactic_by_cases(st, h)
    assert out is not None
    assert len(get_holes(out.term)) == 2


def test_collect_hole_judgments_if_branches_share_goal():
    b = Name("b", 0)
    ctx = _prelude_ctx().with_var(b, t_bool)
    ht = Name("t", 0)
    he = Name("e", 0)
    term = If(
        Var(b, _loc),
        Annotation(Hole(ht), t_int, loc=_loc),
        Annotation(Hole(he), t_int, loc=_loc),
        loc=_loc,
    )
    mp = collect_hole_judgments(ctx, term, t_int, refined_types=True)
    assert set(mp.keys()) == {ht, he}
    for _n, (ety, _c) in mp.items():
        assert ety == t_int


def test_choose_literal_unsat_refinement_returns_none():
    ctx = _prelude_ctx()
    h = Name("h", 0)
    gty = parse_type(r"{z:Int | z > 0 && z < 0}")
    term = Annotation(Hole(h), gty, loc=_loc)
    st = TacticState(ctx, term, gty)
    assert tactic_choose_literal(st, h) is None


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
