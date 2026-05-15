"""Tests for the Liquid Tree Automata synthesizer (arXiv:2605.13456)."""

from __future__ import annotations

from aeon.core.parser import parse_type
from aeon.core.terms import Term, TypeApplication, Var
from aeon.core.types import AbstractionType, t_bool, t_int
from aeon.synthesis.modules.lta.automaton import (
    KIND_BASE_REF,
    KIND_TYPE_ABS,
    LTA,
    Symbol,
    State,
    Transition,
    denot_state,
    language,
    nonempty_finals,
)
from aeon.synthesis.modules.lta.constraints import (
    AEntail,
    AEq,
    CAtom,
    CSubst,
    Position,
    Substitution,
    atoms_in,
    conj,
)
from aeon.synthesis.modules.lta.construction import (
    TypeContextLTA,
    e_app,
    e_const,
    e_tapp,
    e_var,
    q_goal,
    wf_type,
)
from aeon.synthesis.modules.lta.cyclic import (
    build_universe,
    find_cycle_states,
    well_formed_constraints,
)
from aeon.synthesis.modules.lta.polymorphism import (
    collect_type_universe,
    is_polymorphic,
    monomorphize,
)
from aeon.synthesis.modules.lta.reductions import minimize, prune, similarity
from aeon.synthesis.modules.lta.synthesizer import LTASynthesizer
from aeon.synthesis.modules.synthesizerfactory import make_synthesizer
from aeon.typechecking.context import TypeConstructorBinder, TypingContext, VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.utils.name import Name


def test_position_concatenation():
    p = Position() / "type" / "ref"
    assert p == Position(("type", "ref"))
    assert repr(p) == "type.ref"


def test_constraint_atom_flattening():
    a = CAtom(AEq(Position(("x",)), Position(("y",))))
    b = CAtom(AEntail(Position(("u",)), Position(("v",))))
    combined = conj(a, b)
    flat = atoms_in(combined)
    assert any(isinstance(x, AEq) for x in flat)
    assert any(isinstance(x, AEntail) for x in flat)


def test_constraint_subst_pushdown():
    p1 = Position(("u",))
    p2 = Position(("v",))
    theta = (Substitution(target=Position(("a",)), source=Position(("b",))),)
    inner = CAtom(AEntail(p1, p2))
    wrapped = CSubst(theta, inner)
    flat = atoms_in(wrapped)
    assert len(flat) == 1
    entail = flat[0]
    assert isinstance(entail, AEntail)
    assert entail.theta == theta


def test_wf_type_caches_states():
    lta = LTA()
    ctx = TypeContextLTA.empty()
    ty = parse_type(r"{v:Int | v > 0}")
    q1 = wf_type(lta, ctx, ty)
    q2 = wf_type(lta, ctx, ty)
    assert q1 is q2
    base_ref_transitions = [t for t in lta.transitions if t.symbol.kind == KIND_BASE_REF]
    assert len(base_ref_transitions) == 1


def test_e_var_creates_expression_state_with_type():
    from aeon.synthesis.modules.lta.automaton import denot_state

    lta = LTA()
    ctx = TypeContextLTA.empty()
    name = Name("x", 0)
    ty = parse_type(r"{v:Int | v > 0}")
    q = e_var(lta, ctx, name, ty)
    assert not q.is_type_state
    assert q.aeon_type == ty
    ds = denot_state(lta, q)
    assert any(isinstance(d, Var) and d.name == name for d in ds)


def test_e_app_requires_subtype_argument():
    lta = LTA()
    tctx = TypeContextLTA.empty()
    # f : (x : {v:Int | v > 0}) -> {r:Int | r > 0}
    fname = Name("f", 0)
    fty = parse_type(r"(x:{v:Int | v > 0}) -> {r:Int | r > 0}")
    # x : {v:Int | v > 5} — subtype of {v:Int | v > 0}
    xname = Name("x", 0)
    xty = parse_type(r"{v:Int | v > 5}")
    ctx = TypingContext([VariableBinder(fname, fty), VariableBinder(xname, xty)])
    q_f = e_var(lta, tctx, fname, fty)
    q_a = e_var(lta, tctx, xname, xty)
    q_app = e_app(lta, tctx, q_f, q_a, ctx)
    assert q_app is not None
    # Wrong direction: a too-loose argument is rejected.
    yname = Name("y", 0)
    yty = parse_type(r"{v:Int | true}")
    ctx2 = ctx.with_var(yname, yty)
    q_b = e_var(lta, tctx, yname, yty)
    assert e_app(lta, tctx, q_f, q_b, ctx2) is None


def test_q_goal_promotes_subtype_candidates_to_final():
    lta = LTA()
    tctx = TypeContextLTA.empty()
    xname = Name("x", 0)
    xty = parse_type(r"{v:Int | v > 5}")
    goal_ty = parse_type(r"{v:Int | v > 0}")
    ctx = TypingContext([VariableBinder(xname, xty)])
    q_x = e_var(lta, tctx, xname, xty)
    q_g = q_goal(lta, tctx, goal_ty, q_x, ctx)
    assert q_g is not None
    finals = nonempty_finals(lta)
    assert q_g in finals
    terms = language(lta)
    assert any(isinstance(t, Var) and t.name == xname for t in terms)


def test_prune_drops_unsatisfiable_transition():
    """Manually wire an `app` transition whose argument violates the formal
    type, then check Prune removes it."""
    lta = LTA()
    tctx = TypeContextLTA.empty()
    fname = Name("f", 0)
    fty = parse_type(r"(x:{v:Int | v > 100}) -> {r:Int | r > 0}")
    aname = Name("a", 0)
    aty = parse_type(r"{v:Int | v > 0}")
    ctx = TypingContext([VariableBinder(fname, fty), VariableBinder(aname, aty)])
    q_f = e_var(lta, tctx, fname, fty)
    q_a = e_var(lta, tctx, aname, aty)

    # Bypass the subtype gate in e_app and directly inject the app transition.
    from aeon.synthesis.modules.lta.automaton import KIND_APP, State, Transition

    result_ty = parse_type(r"{r:Int | r > 0}")
    q_tau = wf_type(lta, tctx, result_ty)
    q_app = State(label="forced-app", aeon_type=result_ty)
    lta.add_state(q_app)
    arg_pos = Position(("a",))
    fun_pos = Position(("f",))
    constraint = CAtom(AEntail(arg_pos / "type" / "ref", fun_pos / "in" / "type" / "ref"))
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_APP, arity=3),
            incoming=(q_tau, q_f, q_a),
            target=q_app,
            constraint=constraint,
        )
    )
    pruned = prune(lta, ctx)
    # The app transition should have been removed because aty (v > 0) does
    # not entail (v > 100).
    kinds = {t.symbol.kind for t in pruned.transitions}
    assert KIND_APP not in kinds


def test_similarity_merges_subtypes():
    lta = LTA()
    tctx = TypeContextLTA.empty()
    name = Name("v", 0)
    strict_ty = parse_type(r"{v:Int | v > 100}")
    loose_ty = parse_type(r"{v:Int | v > 0}")
    ctx = TypingContext([VariableBinder(name, strict_ty)])
    e_var(lta, tctx, name, strict_ty)
    e_const(lta, tctx, 7, loose_ty)
    eq = similarity(lta, ctx)
    # strict <: loose should yield at least one pair
    assert any(True for _ in eq)
    pruned = prune(lta, ctx)
    minimized, eq_after = minimize(pruned, eq)
    assert eq_after == set()


def test_lta_synthesizer_picks_existing_var():
    """The simplest end-to-end use: with a variable in context that already
    has the goal type, the LTA must return a valid Int term — either the
    bound variable itself or one of the seeded Int constants."""
    from aeon.core.terms import Literal

    xname = Name("x", 0)
    xty = t_int
    ctx = TypingContext([VariableBinder(xname, xty)])
    syn = LTASynthesizer()

    def validate(t: Term) -> bool:
        return check_type(ctx, t, t_int)

    def evaluate(t: Term) -> list[float]:
        return [0.0]

    got = syn.synthesize(
        ctx=ctx,
        type=t_int,
        validate=validate,
        evaluate=evaluate,
        fun_name=Name("main", 0),
        metadata={},
        budget=4.0,
    )
    assert got is not None
    assert isinstance(got, (Var, Literal))
    if isinstance(got, Var):
        assert got.name == xname
    assert check_type(ctx, got, t_int)


def test_factory_returns_lta():
    s = make_synthesizer("lta")
    assert isinstance(s, LTASynthesizer)


# --- Polymorphism (Paper §3.2 footnote 5) ---------------------------------


def test_is_polymorphic_detects_forall():
    assert is_polymorphic(parse_type("forall a:B, (x:a) -> a"))
    assert not is_polymorphic(parse_type("(x:Int) -> Int"))
    assert not is_polymorphic(t_int)


def test_collect_type_universe_includes_builtins_and_goal():
    ctx = TypingContext()
    goal = parse_type(r"{v:Int | v > 0}")
    universe = collect_type_universe(ctx, goal)
    names = {repr(t) for t in universe}
    assert any("Int" in n for n in names)
    assert any("Bool" in n for n in names)


def test_monomorphize_instantiates_type_variable():
    poly = parse_type("forall a:B, (x:a) -> a")
    universe = collect_type_universe(TypingContext(), t_int)
    insts = monomorphize(Name("id", 0), poly, universe)
    # One instantiation per concrete type in the universe.
    assert len(insts) == len(universe)
    for inst in insts:
        assert isinstance(inst.term, TypeApplication)
        # The instantiated type is no longer polymorphic.
        assert not is_polymorphic(inst.mono_type)
        assert isinstance(inst.mono_type, AbstractionType)


def test_monomorphize_non_polymorphic_is_identity():
    insts = monomorphize(Name("x", 0), t_int, [t_int])
    assert len(insts) == 1
    assert isinstance(insts[0].term, Var)
    assert insts[0].mono_type == t_int


def test_monomorphize_refinement_polymorphism_yields_concrete():
    from aeon.core.types import RefinementPolymorphism

    # forall <p:Int -> Bool>, (x:Int) -> Int  — built directly since the core
    # parser does not surface refinement-polymorphism syntax.
    rpoly = RefinementPolymorphism(Name("p", 0), t_int, parse_type("(x:Int) -> Int"))
    insts = monomorphize(Name("g", 0), rpoly, [t_int])
    assert len(insts) >= 1
    for inst in insts:
        assert not is_polymorphic(inst.mono_type)


# --- Cyclic LTA (Paper §5) ------------------------------------------------


def test_build_universe_creates_cyclic_states():
    ctx = TypingContext()
    # A polymorphic list constructor — gives qt a self-cycle.
    ctx.entries.append(TypeConstructorBinder(Name("List", 0), [Name("a", 0)]))
    lta = LTA()
    universe = build_universe(lta, ctx, [t_int, t_bool])
    cycles = find_cycle_states(lta)
    # Both universe states participate in a cycle.
    assert universe.qt.id in cycles
    assert universe.qphi.id in cycles


def test_universe_without_poly_constructor_still_cycles_via_qphi():
    """qϕ always has cyclic ∧/∨ edges even with no polymorphic constructors."""
    lta = LTA()
    universe = build_universe(lta, TypingContext(), [t_int])
    cycles = find_cycle_states(lta)
    assert universe.qphi.id in cycles


def test_acyclic_constraint_restriction_holds_for_universe():
    lta = LTA()
    build_universe(lta, TypingContext(), [t_int, t_bool])
    ok, violations = well_formed_constraints(lta)
    # The universe has no constrained transitions, so the restriction holds.
    assert ok
    assert violations == []


def test_acyclic_constraint_restriction_detects_violation():
    """A transition whose constraint references a cycle state must be flagged."""
    lta = LTA()
    universe = build_universe(lta, TypingContext(), [t_int])
    # Forge a constrained transition that consumes the cyclic qϕ state.
    target = State(label="bad", is_type_state=True)
    lta.add_state(target)
    constraint = CAtom(AEntail(Position(("x",)), Position(("y",))))
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_BASE_REF, arity=1),
            incoming=(universe.qphi,),
            target=target,
            constraint=constraint,
        )
    )
    ok, violations = well_formed_constraints(lta)
    assert not ok
    assert len(violations) == 1


def test_wf_type_on_polymorphism_wires_into_universe():
    # A polymorphic List constructor makes qt genuinely cyclic (§5).
    ctx = TypingContext()
    ctx.entries.append(TypeConstructorBinder(Name("List", 0), [Name("a", 0)]))
    lta = LTA()
    tctx = TypeContextLTA.empty()
    tctx.universe = build_universe(lta, ctx, [t_int])
    poly = parse_type("forall a:B, (x:a) -> a")
    q_poly = wf_type(lta, tctx, poly)
    assert q_poly.is_type_state and q_poly.aeon_type == poly
    # The type-abstraction transition exists and has the universe qt as an
    # incoming state — the type variable `a` resolves to the cyclic universe.
    tabs = [t for t in lta.transitions if t.symbol.kind == KIND_TYPE_ABS]
    assert len(tabs) == 1
    assert tctx.universe.qt in tabs[0].incoming
    # qt participates in a cycle, and the polymorphic type depends on it.
    cycles = find_cycle_states(lta)
    assert tctx.universe.qt.id in cycles


def test_e_tapp_creates_monomorphic_state():
    lta = LTA()
    tctx = TypeContextLTA.empty()
    tctx.universe = build_universe(lta, TypingContext(), [t_int])
    poly = parse_type("forall a:B, (x:a) -> a")
    universe = collect_type_universe(TypingContext(), t_int)
    insts = monomorphize(Name("id", 0), poly, universe)
    inst = insts[0]
    q = e_tapp(lta, tctx, inst.term, inst.mono_type)
    assert not q.is_type_state
    assert q.aeon_type == inst.mono_type
    # The denotation materializes the TypeApplication spine.
    ds = denot_state(lta, q)
    assert any(isinstance(d, TypeApplication) for d in ds)


def test_denotation_is_cycle_safe():
    """Denotation over the cyclic universe must terminate (bounded unrolling)."""
    lta = LTA()
    universe = build_universe(lta, TypingContext(), [t_int])
    # qphi is a type state, so its term-denotation is empty by definition,
    # but the call must terminate rather than recurse forever.
    assert denot_state(lta, universe.qphi) == []


def test_synthesizer_handles_polymorphic_binding_in_context():
    """With a polymorphic identity function in Γ, synthesis still succeeds —
    the synthesizer instantiates it rather than crashing or filtering Γ down
    to nothing."""
    from aeon.core.terms import Literal

    idname = Name("idf", 0)
    idty = parse_type("forall a:B, (x:a) -> a")
    nname = Name("n", 0)
    ctx = TypingContext([VariableBinder(idname, idty), VariableBinder(nname, t_int)])
    syn = LTASynthesizer()

    def validate(t: Term) -> bool:
        return check_type(ctx, t, t_int)

    def evaluate(t: Term) -> list[float]:
        return [0.0]

    got = syn.synthesize(
        ctx=ctx,
        type=t_int,
        validate=validate,
        evaluate=evaluate,
        fun_name=Name("main", 0),
        metadata={},
        budget=8.0,
    )
    assert got is not None
    assert isinstance(got, (Var, Literal, TypeApplication))
    assert check_type(ctx, got, t_int)
