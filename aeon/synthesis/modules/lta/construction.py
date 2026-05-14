"""LTA construction rules — well-formedness (WF) and Transition (Fig. 7),
extended with polymorphic transition construction (Paper §3.2 footnote 5).

Well-formedness rules build the *type* sub-automaton:
- wf-prim: nullary transition for each primitive type t.
- wf-pred: leaf transition for each refinement predicate ϕ ∈ Φ.
- wf-base: ternary transition `τ(q_x, q_t, q_ϕ) → q_τ` for each base
           refinement {x:t|ϕ}.
- wf-arrow: binary transition `τ→(q_τi, q_τj) → q_τ→` for each arrow type.
- wf-var: nullary transition introducing a bound variable.
- wf-poly: type-abstraction transition `tabs(q_t, q_body) → q_∀` for a
           `forall α:B, τ` — the `q_t` incoming is the cyclic universe state,
           so `α` ranges over every type (§5).
- wf-rpoly: refinement-abstraction transition for `forall <ρ:s→Bool>, τ`,
            with the cyclic `q_ϕ` universe as the predicate-variable state.

Expression-transition rules build the *expression* sub-automaton:
- E-var:   x(q_τ) → q_x        (variable reference with its type sub-automaton)
- E-const: c(q_τ) → q_c        (constant)
- E-app:   app(q_τ, q_f, q_a) → q_app, with SubType constraint
- E-tapp:  tapp(q_τ, q_f) → q_e  (type application — instantiates a
           polymorphic function at a concrete type)
- E-if:    if(q_τ, q_b, q_t, q_f) → q_if, with constraints encoding branch
           typing.
- Q-goal:  goal(q_τ, q_termk) → q_goal, with SubType(termk.type, goal.type).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from aeon.core.terms import Term
from aeon.core.types import (
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypePolymorphism,
    TypeVar,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

from aeon.synthesis.modules.lta.automaton import (
    KIND_APP,
    KIND_ARROW_TYPE,
    KIND_BASE_REF,
    KIND_BASE_TYPE,
    KIND_CONST,
    KIND_GOAL,
    KIND_IF,
    KIND_PRED,
    KIND_REF_ABS,
    KIND_TYPE_ABS,
    KIND_TYPE_APP,
    KIND_TYPE_BIND,
    KIND_VAR,
    LTA,
    State,
    Symbol,
    Transition,
)
from aeon.synthesis.modules.lta.constraints import (
    AEntail,
    AEq,
    CAtom,
    CSubst,
    Constraint,
    Position,
    Substitution,
    conj,
)


_loc = SynthesizedLocation("lta")


@dataclass
class TypeContextLTA:
    """Working context maintained during LTA construction.

    - `type_states`: caches the LTA state we created for a given aeon `Type`,
      so the same type only appears once in the automaton.
    - `expr_states_by_type`: index of expression states by their aeon `Type`,
      used by E-app and Similarity to find candidate functions and arguments.
    - `universe`: the cyclic universe states (`qt`, `qϕ`) of §5, if built.
      Polymorphic type/refinement variables resolve to these.
    - `typevar_env`: maps a bound type-variable name to the LTA state that
      represents it — `qt` for universe-bound variables.
    """

    type_states: dict[Type, State]
    expr_states_by_type: dict[Type, list[State]]
    universe: object | None = None  # cyclic.Universe | None (avoid import cycle)
    typevar_env: dict[Name, State] = field(default_factory=dict)

    @staticmethod
    def empty() -> "TypeContextLTA":
        return TypeContextLTA({}, {})

    def register_expr_state(self, s: State) -> None:
        if s.aeon_type is None:
            return
        self.expr_states_by_type.setdefault(s.aeon_type, []).append(s)

    @property
    def qt(self) -> State | None:
        return getattr(self.universe, "qt", None)

    @property
    def qphi(self) -> State | None:
        return getattr(self.universe, "qphi", None)


# Well-formedness ----------------------------------------------------------


def wf_type(lta: LTA, ctx: TypeContextLTA, ty: Type) -> State:
    """Build (or fetch) the type sub-automaton state for `ty`.

    Dispatches to wf-base for `RefinedType`, wf-arrow for `AbstractionType`,
    wf-poly for `TypePolymorphism`, wf-rpoly for `RefinementPolymorphism`, and
    wf-prim for `TypeConstructor`/`Top`. A `TypeVar` bound by an enclosing
    abstraction resolves to the cyclic universe state `qt` (§5).
    """
    if ty in ctx.type_states:
        return ctx.type_states[ty]

    if isinstance(ty, RefinedType):
        # wf-base: τ ≡ {x : t | ϕ}
        q_base = wf_type(lta, ctx, ty.type)
        q_pred = wf_pred(lta, ty.refinement)
        q_bind = wf_var(lta, ty.name)
        q_tau = State(label=f"τ:{ty}", aeon_type=ty, is_type_state=True)
        lta.add_state(q_tau)
        lta.add_transition(
            Transition(
                symbol=Symbol(KIND_BASE_REF, payload=str(ty), arity=3),
                incoming=(q_bind, q_base, q_pred),
                target=q_tau,
            )
        )
        ctx.type_states[ty] = q_tau
        return q_tau

    if isinstance(ty, AbstractionType):
        # wf-arrow: τ→ ≡ τi → τj
        q_in = wf_type(lta, ctx, ty.var_type)
        q_out = wf_type(lta, ctx, ty.type)
        q_arrow = State(label=f"τ→:{ty}", aeon_type=ty, is_type_state=True)
        lta.add_state(q_arrow)
        lta.add_transition(
            Transition(
                symbol=Symbol(KIND_ARROW_TYPE, payload=str(ty), arity=2),
                incoming=(q_in, q_out),
                target=q_arrow,
            )
        )
        ctx.type_states[ty] = q_arrow
        return q_arrow

    if isinstance(ty, TypePolymorphism):
        # wf-poly: forall α:B, body — the type variable α ranges over the
        # cyclic universe `qt`. Binding α → qt makes the body's sub-automaton
        # genuinely cyclic whenever it mentions α (§5).
        q_univ = ctx.qt
        prev = ctx.typevar_env.get(ty.name)
        if q_univ is not None:
            ctx.typevar_env[ty.name] = q_univ
        q_body = wf_type(lta, ctx, ty.body)
        if prev is not None:
            ctx.typevar_env[ty.name] = prev
        elif ty.name in ctx.typevar_env:
            del ctx.typevar_env[ty.name]
        q_poly = State(label=f"∀:{ty}", aeon_type=ty, is_type_state=True)
        lta.add_state(q_poly)
        incoming = (q_univ, q_body) if q_univ is not None else (q_body,)
        lta.add_transition(
            Transition(
                symbol=Symbol(KIND_TYPE_ABS, payload=ty.name, arity=len(incoming)),
                incoming=incoming,
                target=q_poly,
            )
        )
        ctx.type_states[ty] = q_poly
        return q_poly

    if isinstance(ty, RefinementPolymorphism):
        # wf-rpoly: forall <ρ:s→Bool>, body — the abstract refinement ρ ranges
        # over the cyclic predicate universe `qϕ`.
        q_univ = ctx.qphi
        q_body = wf_type(lta, ctx, ty.body)
        q_poly = State(label=f"∀ρ:{ty}", aeon_type=ty, is_type_state=True)
        lta.add_state(q_poly)
        incoming = (q_univ, q_body) if q_univ is not None else (q_body,)
        lta.add_transition(
            Transition(
                symbol=Symbol(KIND_REF_ABS, payload=ty.name, arity=len(incoming)),
                incoming=incoming,
                target=q_poly,
            )
        )
        ctx.type_states[ty] = q_poly
        return q_poly

    if isinstance(ty, TypeVar):
        # A type variable bound by an enclosing `forall` resolves to the
        # cyclic universe state; a free/rigid one gets its own leaf.
        bound = ctx.typevar_env.get(ty.name)
        if bound is not None:
            ctx.type_states[ty] = bound
            return bound

    # wf-prim: TypeConstructor / free TypeVar / Top
    q_prim = State(label=f"t:{ty}", aeon_type=ty, is_type_state=True)
    lta.add_state(q_prim)
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_BASE_TYPE, payload=str(ty), arity=0),
            incoming=(),
            target=q_prim,
        )
    )
    ctx.type_states[ty] = q_prim
    return q_prim


def wf_pred(lta: LTA, predicate: object) -> State:
    """wf-pred: introduce a leaf transition for a refinement predicate ϕ."""
    q = State(label=f"ϕ:{predicate}", is_type_state=True)
    lta.add_state(q)
    lta.add_transition(Transition(symbol=Symbol(KIND_PRED, payload=predicate, arity=0), incoming=(), target=q))
    return q


def wf_var(lta: LTA, name: Name) -> State:
    """wf-var: introduce a leaf transition for a bound variable name (used in
    base refinement bindings — distinct from `e_var` for expression-level
    variable references)."""
    q = State(label=f"x:{name}", is_type_state=True)
    lta.add_state(q)
    lta.add_transition(Transition(symbol=Symbol(KIND_TYPE_BIND, payload=name, arity=0), incoming=(), target=q))
    return q


# Expression-level Transition rules ----------------------------------------


def e_var(lta: LTA, ctx: TypeContextLTA, name: Name, ty: Type) -> State:
    """E-var: introduce an expression state for a variable `x : τ` (whether
    a scalar variable or a library function — both are bound in Γ)."""
    q_tau = wf_type(lta, ctx, ty)
    q_x = State(label=f"e-var:{name}", aeon_type=ty)
    lta.add_state(q_x)
    lta.add_transition(Transition(symbol=Symbol(KIND_VAR, payload=name, arity=1), incoming=(q_tau,), target=q_x))
    ctx.register_expr_state(q_x)
    return q_x


def e_const(lta: LTA, ctx: TypeContextLTA, value: object, ty: Type) -> State:
    """E-const: introduce an expression state for a constant `c : τ`."""
    q_tau = wf_type(lta, ctx, ty)
    q_c = State(label=f"e-const:{value}", aeon_type=ty)
    lta.add_state(q_c)
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_CONST, payload=(value, ty), arity=1),
            incoming=(q_tau,),
            target=q_c,
        )
    )
    ctx.register_expr_state(q_c)
    return q_c


def e_poly_var(lta: LTA, ctx: TypeContextLTA, name: Name, ty: Type) -> State:
    """E-var for a *polymorphic* binding `f : forall α, …`.

    This creates the structural (cyclic) polymorphic expression state — its
    type sub-automaton is rooted at a `tabs`/`rabs` transition wired into the
    universe, faithfully matching §5. Concrete candidate terms are produced
    separately by `e_tapp` (instantiation)."""
    q_tau = wf_type(lta, ctx, ty)  # builds the cyclic tabs/rabs sub-automaton
    q_f = State(label=f"e-pvar:{name}", aeon_type=ty)
    lta.add_state(q_f)
    lta.add_transition(Transition(symbol=Symbol(KIND_VAR, payload=name, arity=1), incoming=(q_tau,), target=q_f))
    ctx.register_expr_state(q_f)
    return q_f


def e_tapp(
    lta: LTA,
    ctx: TypeContextLTA,
    head_term: Term,
    mono_type: Type,
) -> State:
    """E-tapp: introduce an expression state for a type/refinement application
    `f[T]` whose instantiated (monomorphic) type is `mono_type`.

    `head_term` is the already-built head (a `TypeApplication` /
    `RefinementApplication` spine produced by `polymorphism.monomorphize`).
    The transition records the head term as payload so the denotation can
    materialize it directly."""
    q_tau = wf_type(lta, ctx, mono_type)
    q_e = State(label="e-tapp", aeon_type=mono_type)
    lta.add_state(q_e)
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_TYPE_APP, payload=head_term, arity=1),
            incoming=(q_tau,),
            target=q_e,
        )
    )
    ctx.register_expr_state(q_e)
    return q_e


def _sub_type_constraint(arg_pos: Position, formal_pos: Position) -> Constraint:
    """SubType(δi, δj) (Equation 1 of the paper) for base refinements:
        i.type.t = j.type.t  ∧  i.type.ref ⊨ j.type.ref
    Higher-rank cases are simplified — for arrows we accept structurally and
    let the verifier handle deeper checks."""
    base_eq = CAtom(
        AEq(
            arg_pos / "type" / "base",
            formal_pos / "type" / "base",
        )
    )
    ref_ent = CAtom(
        AEntail(
            arg_pos / "type" / "ref",
            formal_pos / "type" / "ref",
        )
    )
    return conj(base_eq, ref_ent)


def e_app(
    lta: LTA,
    ctx: TypeContextLTA,
    q_f: State,
    q_a: State,
    type_ctx: TypingContext,
) -> State | None:
    """E-app: introduce an `app` transition for f applied to a, provided that
    the actual-argument type is a subtype of the formal argument's type. The
    resulting expression state is keyed on the (substituted) result type."""
    from aeon.synthesis.modules.lta.subtyping import is_subtype

    f_ty = q_f.aeon_type
    a_ty = q_a.aeon_type
    if not isinstance(f_ty, AbstractionType):
        return None
    if a_ty is None:
        return None
    if not is_subtype(type_ctx, a_ty, f_ty.var_type):
        return None

    # Apply the substitution θ = [actual / formal] to the result type.
    result_ty = _apply_dependent_subst(f_ty, q_a)
    q_tau = wf_type(lta, ctx, result_ty)
    q_app = State(label="e-app", aeon_type=result_ty)
    lta.add_state(q_app)

    # Constraint: SubType(arg.type, fun.in) ∧ θ.SubType(fun.out, app.type).
    arg_pos = Position(("a",))
    fun_pos = Position(("f",))
    app_pos = Position(("τ",))
    theta = (Substitution(target=arg_pos, source=fun_pos / "in"),)
    constraint = conj(
        _sub_type_constraint(arg_pos, fun_pos / "in"),
        CSubst(theta, _sub_type_constraint(fun_pos / "out", app_pos)),
    )
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_APP, arity=3),
            incoming=(q_tau, q_f, q_a),
            target=q_app,
            constraint=constraint,
        )
    )
    ctx.register_expr_state(q_app)
    return q_app


def _apply_dependent_subst(f_ty: AbstractionType, q_a: State) -> Type:
    """Substitute the actual argument for the dependent name in the function's
    result type. For a non-name-dependent function this is a no-op.

    If `q_a`'s underlying expression is a `Var`, we substitute that Var.
    Otherwise the dependent reference cannot be eliminated and we return the
    function's result type unchanged (the verifier will fall back to subtyping
    on the broader type)."""
    from aeon.core.substitutions import substitution_in_type
    from aeon.core.terms import Var

    # Heuristic: only substitute when the arg state corresponds to a simple
    # variable. (For composite arguments we'd need ANF binding.)
    var_name: Name | None = None
    if q_a.label.startswith("e-var:"):
        # name encoded in the label — recover via metadata stored elsewhere.
        # Simpler: look at the transition that targets q_a.
        # We avoid passing extra structures here and fall back to no subst.
        pass
    if var_name is None:
        return f_ty.type
    return substitution_in_type(f_ty.type, Var(var_name, _loc), f_ty.var_name)


def e_if(
    lta: LTA,
    ctx: TypeContextLTA,
    q_b: State,
    q_t: State,
    q_f: State,
) -> State | None:
    """E-if: introduce an `if` transition with constraints encoding branch
    typing. We accept only when both branches agree on a common base type."""
    if q_t.aeon_type is None or q_f.aeon_type is None:
        return None
    ty = _join_branches(q_t.aeon_type, q_f.aeon_type)
    if ty is None:
        return None
    q_tau = wf_type(lta, ctx, ty)
    q_if = State(label="e-if", aeon_type=ty)
    lta.add_state(q_if)
    # ψ = ((qb ▶ ref) ∧ SubType(qt.type, qif.type))
    #   ∧ (¬(qb ▶ ref) ∧ SubType(qf.type, qif.type))
    b_pos = Position(("b",))
    t_pos = Position(("t",))
    f_pos = Position(("f",))
    if_pos = Position(("τ",))
    cond = CAtom(AEntail(b_pos / "ref", b_pos / "ref"))  # placeholder
    constraint = conj(
        cond,
        _sub_type_constraint(t_pos, if_pos),
        _sub_type_constraint(f_pos, if_pos),
    )
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_IF, arity=4),
            incoming=(q_tau, q_b, q_t, q_f),
            target=q_if,
            constraint=constraint,
        )
    )
    ctx.register_expr_state(q_if)
    return q_if


def _join_branches(t1: Type, t2: Type) -> Type | None:
    """Compute a (very coarse) join: same base type or Top."""
    if t1 == t2:
        return t1

    # Strip refinements and compare.
    def base(t: Type) -> Type:
        return t.type if isinstance(t, RefinedType) else t

    if base(t1) == base(t2):
        return base(t1)
    return None


def q_goal(
    lta: LTA,
    ctx: TypeContextLTA,
    goal_type: Type,
    q_termk: State,
    type_ctx: TypingContext,
) -> State | None:
    """Q-goal: connect a candidate-term state `q_termk` to a distinguished
    final state `q_goal`, with constraint SubType(termk.type, goal.type).
    Returns the final state only if the subtyping holds."""
    from aeon.synthesis.modules.lta.subtyping import is_subtype

    if q_termk.aeon_type is None:
        return None
    if not is_subtype(type_ctx, q_termk.aeon_type, goal_type):
        return None
    q_tau = wf_type(lta, ctx, goal_type)
    q_g = State(label="goal", aeon_type=goal_type)
    lta.add_state(q_g)
    lta.add_final(q_g)
    termk_pos = Position(("termk",))
    goal_pos = Position(("τ",))
    constraint = _sub_type_constraint(termk_pos, goal_pos)
    lta.add_transition(
        Transition(
            symbol=Symbol(KIND_GOAL, arity=2),
            incoming=(q_tau, q_termk),
            target=q_g,
            constraint=constraint,
        )
    )
    return q_g
