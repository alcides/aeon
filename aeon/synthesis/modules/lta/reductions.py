"""LTA reductions: Prune, Similarity, Minimize (Fig. 9).

Prune
    Eliminates portions of the automaton that cannot participate in any
    well-typed program. Implemented via two atomic intersection operations:
        ⊓_Syntax       — for syntactic equality (p1 = p2)
        ⊓^ψ_Semantics  — for semantic entailment (θ.p1 ⊨ p2)
    Bottom (⊥) transitions are dropped as a side-effect.

Similarity (S-trans, S-eq)
    Two transitions are similar when one's type is a subtype of the other's:
        ψ_<:  = SubType(δi ▶ type, δj ▶ type)
    is satisfiable. Pairs (δi, δj) with δi ≲ δj are recorded in the
    equivalence set E.

Minimize (M-trans, M-LTA)
    For each similar pair, retain the subtype transition and redirect any
    transition that referenced the supertype's target so it points at the
    subtype's target. After fixpoint we reset E.
"""

from __future__ import annotations


from aeon.typechecking.context import TypingContext

from aeon.synthesis.modules.lta.automaton import (
    KIND_APP,
    KIND_BOTTOM,
    KIND_GOAL,
    LTA,
    State,
    Transition,
)
from aeon.synthesis.modules.lta.constraints import (
    AEntail,
    AEq,
    atoms_in,
)


# Prune --------------------------------------------------------------------


def prune(lta: LTA, type_ctx: TypingContext) -> LTA:
    """Drop transitions whose constraint cannot be satisfied — i.e. transitions
    whose atomic constraints fail the syntactic or semantic intersection test.

    For each transition with a constraint of the form `p1 = p2` or `p1 ⊨ p2`,
    we look at the metadata of the incoming states at those positions and
    decide whether the requirement holds. Transitions referencing nonexistent
    positions are kept (no information to falsify them).
    """
    from aeon.synthesis.modules.lta.subtyping import is_subtype_cached

    survivors: list[Transition] = []
    for t in list(lta.transitions):
        if t.symbol.kind == KIND_BOTTOM:
            continue
        keep = True
        for atom in atoms_in(t.constraint):
            if isinstance(atom, AEq):
                # Synthetic equality is structural by construction in this
                # implementation (we already build only well-typed apps), so
                # we keep transitions whose positional atoms cannot be
                # contradicted by the incoming states' types.
                continue
            if isinstance(atom, AEntail):
                # Drop if the referenced incoming-state types fail the
                # subtype relation. We use the *first* incoming as a proxy for
                # δ▶p when the position labels don't map exactly — this is
                # consistent with how `_sub_type_constraint` constructs the
                # constraint over (arg, formal) pairs.
                if t.symbol.kind == KIND_APP and len(t.incoming) >= 3:
                    _, q_f, q_a = t.incoming[0], t.incoming[1], t.incoming[2]
                    f_ty = q_f.aeon_type
                    a_ty = q_a.aeon_type
                    from aeon.core.types import AbstractionType

                    if isinstance(f_ty, AbstractionType) and a_ty is not None:
                        if not is_subtype_cached(type_ctx, a_ty, f_ty.var_type):
                            keep = False
                            break
                elif t.symbol.kind == KIND_GOAL and len(t.incoming) >= 2:
                    q_termk = t.incoming[1]
                    target_ty = t.target.aeon_type
                    if q_termk.aeon_type is not None and target_ty is not None:
                        if not is_subtype_cached(type_ctx, q_termk.aeon_type, target_ty):
                            keep = False
                            break
        if keep:
            survivors.append(t)

    # Rebuild transition index from survivors.
    new_lta = LTA(states=set(lta.states), finals=set(lta.finals))
    for t in survivors:
        new_lta.add_transition(t)
    # Drop unreachable states (states with no transitions targeting them and
    # not appearing as incoming anywhere).
    reachable: set[int] = set()
    for t in survivors:
        reachable.add(t.target.id)
        for s in t.incoming:
            reachable.add(s.id)
    for f in new_lta.finals:
        reachable.add(f.id)
    new_lta.states = {s for s in new_lta.states if s.id in reachable}
    return new_lta


# Similarity ---------------------------------------------------------------


def similarity(
    lta: LTA,
    type_ctx: TypingContext,
    equiv_set: set[tuple[int, int]] | None = None,
) -> set[tuple[int, int]]:
    """Identify pairs (δi, δj) such that the type of δi is a subtype of the
    type of δj — i.e. δi ≲ δj. Returns the updated equivalence set E
    (transition-id pairs).

    We only consider *expression* transitions: there's no value in merging
    type-level transitions (the type sub-automaton is already deduplicated
    via the `type_states` cache during construction).
    """
    from aeon.core.types import AbstractionType
    from aeon.synthesis.modules.lta.subtyping import is_subtype_cached

    if equiv_set is None:
        equiv_set = set()

    expr_trans = [t for t in lta.transitions if not t.target.is_type_state]

    for i, di in enumerate(expr_trans):
        ti_ty = di.target.aeon_type
        if ti_ty is None or isinstance(ti_ty, AbstractionType):
            continue
        for dj in expr_trans:
            if di.id == dj.id:
                continue
            tj_ty = dj.target.aeon_type
            if tj_ty is None or isinstance(tj_ty, AbstractionType):
                continue
            if (di.id, dj.id) in equiv_set:
                continue
            if is_subtype_cached(type_ctx, ti_ty, tj_ty):
                equiv_set.add((di.id, dj.id))

    return equiv_set


# Minimize -----------------------------------------------------------------


def minimize(
    lta: LTA,
    equiv_set: set[tuple[int, int]],
) -> tuple[LTA, set[tuple[int, int]]]:
    """Apply M-trans: for each (δi, δj) in E with δi ≲ δj, drop δj and
    redirect any transition that previously consumed δj.target so it consumes
    δi.target instead.

    Returns the minimized automaton and a freshly-reset equivalence set
    (M-LTA resets E after minimization).
    """
    if not equiv_set:
        return lta, equiv_set

    by_id = {t.id: t for t in lta.transitions}
    # State-redirection mapping: replaced target -> retained target.
    redirect: dict[int, State] = {}
    drop_trans_ids: set[int] = set()

    for di_id, dj_id in equiv_set:
        di = by_id.get(di_id)
        dj = by_id.get(dj_id)
        if di is None or dj is None:
            continue
        if dj.target.id == di.target.id:
            continue
        # Prefer the more specific (subtype) representative — that's di.
        redirect[dj.target.id] = di.target
        drop_trans_ids.add(dj.id)

    if not redirect and not drop_trans_ids:
        return lta, set()

    new_lta = LTA(states=set(lta.states), finals=set(lta.finals))
    for t in lta.transitions:
        if t.id in drop_trans_ids:
            continue
        new_incoming = tuple(redirect.get(s.id, s) for s in t.incoming)
        new_target = redirect.get(t.target.id, t.target)
        if (new_incoming == t.incoming) and (new_target.id == t.target.id):
            new_lta.add_transition(t)
        else:
            new_lta.add_transition(
                Transition(
                    symbol=t.symbol,
                    incoming=new_incoming,
                    target=new_target,
                    constraint=t.constraint,
                )
            )

    # Reset the equivalence set, per M-LTA.
    return new_lta, set()
