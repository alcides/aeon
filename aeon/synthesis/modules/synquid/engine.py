"""Synquid-style type-directed synthesis: goal decomposition + Q-driven guards."""

from __future__ import annotations

from itertools import chain, count, takewhile
import itertools
from typing import Callable

from aeon.core.instantiation import type_substitution
from aeon.core.terms import Abstraction, Annotation, Application, If, Literal, Term, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, Type, TypeConstructor, TypePolymorphism, TypeVar
from aeon.core.types import refined_to_unrefined_type
from aeon.synthesis.modules.symetric.synthesizer import _match_type
from aeon.synthesis.modules.synquid.decompose import synquid_application_arg_types, uncurry
from aeon.synthesis.modules.synquid.guards import (
    bool_pairwise_conjunctions,
    bool_quad_conjunctions,
    bool_terms_from_qualifier_atoms,
    bool_triple_conjunctions,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.typeinfer import check_type
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.utils.name import Name


def monomorfic(t: Type, typing_ctx: TypingContext, t_l: dict[Name, Type]):
    match t:
        case TypePolymorphism(var_name, _, var_body):
            for t in [
                t
                for n, t in typing_ctx.concrete_vars()
                if isinstance(t, TypeConstructor) and t != TypeConstructor(Name("Unit", 0))
            ]:
                t_l[var_name] = t
                for result in monomorfic(var_body, typing_ctx, t_l):
                    yield result
        case AbstractionType(var_name, var_type, typ):
            for in_type in monomorfic(var_type, typing_ctx, t_l):
                for body in monomorfic(typ, typing_ctx, t_l):
                    yield AbstractionType(var_name, in_type, body)
        case TypeVar(var_name):
            yield t_l[var_name]
        case _:
            yield t


def frange(start, stop, step):
    return takewhile(lambda x: x < stop, count(start, step))


def _solve_literal(ret_t: Type, base_t: TypeConstructor):
    """Synquid-faithful literal synthesis. Rather than enumerating a fixed range
    of constants, emit a *symbolic* literal (``?intLit`` / ``?floatLit``) and let
    z3 pick a value satisfying the verification condition present at this
    position -- the refinement of the goal type, propagated here by round-trip
    type checking. Yields the single solved literal, or nothing if the
    refinement is unsatisfiable (no constant inhabits the goal type)."""
    from z3 import Solver, sat

    from aeon.core.liquid import LiquidLiteralBool, liquid_free_vars
    from aeon.verification.smt import make_variable, translate_liq

    if isinstance(ret_t, RefinedType):
        binder, refinement = ret_t.name, ret_t.refinement
    else:
        binder, refinement = Name("_lit", 0), LiquidLiteralBool(True)

    # The binder is the unknown to solve for; any other free variables in the VC
    # are unknown context values, given fresh consts so the binder is solved
    # relative to them.
    variables: dict[str, object] = {str(binder): make_variable(str(binder), base_t)}
    for fv in liquid_free_vars(refinement):
        variables.setdefault(str(fv), make_variable(str(fv), base_t))

    try:
        s = Solver()
        s.add(translate_liq(refinement, variables))
        if s.check() != sat:
            return
        model_val = s.model()[variables[str(binder)]]
    except Exception:
        return

    if base_t.name.name == "Int":
        yield Literal(0 if model_val is None else model_val.as_long(), base_t)
    else:  # Float
        yield Literal(0.0 if model_val is None else float(model_val.as_fraction()), base_t)


def _head_result_constructor(t: Type) -> TypeConstructor | None:
    """Head datatype for ``closing`` when the spine ends in ``TypeConstructor`` or ``RefinedType`` over one."""
    match t:
        case TypeConstructor():
            return t
        case RefinedType(_, inner, _) if isinstance(inner, TypeConstructor):
            return inner
        case _:
            return None


_PRIMITIVE_BASES = {"Int", "Bool", "Float", "String", "Unit"}
# Goals at which a "returns-anything" operator (``∀a. … -> a``: ``+``, ``-``,
# ``*``, ``Array_get``, ...) is meaningful: the Num/Ord arithmetic ops. Building
# them at *non-numeric* primitives produces ill-typed junk -- in particular
# ``True + False`` as a Bool guard, which makes the z3 backend raise an
# int-where-bool sort error and so escapes the local refinement check below.
_NUMERIC_BASES = {"Int", "Float"}


def _refined_adt_param(i: Type) -> bool:
    """True for a refined argument whose base is a user datatype/container (e.g.
    ``{cs: List Chunk | len cs >= 1}``). Such a parameter must be built by
    *application* one level deeper, not as a level-0 leaf -- only primitive
    refined params (refined Int/Bool/...) are satisfiable by literals at level 0."""
    if not isinstance(i, RefinedType):
        return False
    base = refined_to_unrefined_type(i)
    return isinstance(base, TypeConstructor) and base.name.name not in _PRIMITIVE_BASES


def _local_check(ctx: TypingContext, term: Term, goal: Type) -> bool:
    """Round-trip local refinement check (Synquid APPFO, PLDI'16 §3.2).

    Keep an argument candidate unless it is *definitely* incompatible with the
    refined parameter type ``goal``. ``check_type`` returns ``False`` only on a
    genuine refinement contradiction -- e.g. ``nil : {List a | len >= 1}`` -- so
    those candidates are pruned at the point of application instead of after a
    full (and failing) program-level validation. A *raise* (an ill-sorted
    intermediate, or a predicate unknown that only resolves in the global
    context) means the local checker cannot decide: treat it as ``Unknown`` and
    keep the candidate, so pruning never drops a valid term (soundness)."""
    try:
        return bool(check_type(ctx, term, goal))
    except Exception:
        return True


def _pruned(gen, ctx: TypingContext, goal: Type):
    for t in gen:
        if _local_check(ctx, t, goal):
            yield t


def _arg_gen(ctx: TypingContext, level: int, i: Type, skip: Callable[[Name], bool], mem: dict):
    """Candidate generator for one application argument of type ``i``.

    Datatype / refined-container args are built one level deeper; primitive args
    are level-0 leaves. A *refined* container arg additionally goes through the
    round-trip local check, so e.g. an empty list is pruned against a
    ``len >= 1`` parameter before the enclosing application is ever assembled."""
    if isinstance(i, TypeConstructor) or _refined_adt_param(i):
        g = synthes_memory(ctx, level - 1, i, skip, mem)
        return _pruned(g, ctx, i) if _refined_adt_param(i) else g
    return synthes_memory(ctx, 0, i, skip, mem)


def _peel_polymorphism(ty: Type) -> tuple[list[Name], Type]:
    """Strip the ``forall`` prefix, returning the bound type variables and body."""
    tyvars: list[Name] = []
    cur = ty
    while isinstance(cur, TypePolymorphism):
        tyvars.append(cur.name)
        cur = cur.body
    return tyvars, cur


def _uncurry_arrow(ty: Type) -> tuple[list[Type], Type]:
    """Split an arrow type into argument types and return type, tolerating
    type-variable domains (e.g. ``(hd: a) -> (tl: List a) -> List a``) -- which
    arise before a polymorphic binding is instantiated, and which ``uncurry``
    rejects."""
    params: list[Type] = []
    cur = ty
    while isinstance(cur, AbstractionType):
        params.append(cur.var_type)
        cur = cur.type
    return params, cur


def closing(elems: tuple, typ: TypeConstructor):
    if len(elems) == 1:
        return TypeApplication(elems[0], typ)
    else:
        return Application(closing(elems[:-1], typ), elems[-1])


def synthes_memory(ctx: TypingContext, level: int, ret_t: Type, skip: Callable[[Name], bool], mem: dict):
    if (ctx, level, ret_t) in mem:
        yield from mem[(ctx, level, ret_t)]
    else:
        mem[(ctx, level, ret_t)] = []
        try:
            for item in synthes(ctx, level, ret_t, skip, mem):
                mem[(ctx, level, ret_t)].append(item)
                yield item
        except NotImplementedError:
            yield from []


def match_type(t1: Type, t2: Type):
    if t1 == t2:
        return True
    elif type(t1) is type(t2):
        return False
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        return match_type(t1.var_type, t2.var_type) and match_type(t1.type, t2.type)
    else:
        return False


def synthes(ctx: TypingContext, level: int, ret_t: Type, skip: Callable[[Name], bool], mem: dict):
    base_t = refined_to_unrefined_type(ret_t)
    if level == 0:
        arrow_goal: AbstractionType | None = ret_t if isinstance(ret_t, AbstractionType) else None
        if arrow_goal is None and isinstance(ret_t, RefinedType) and isinstance(ret_t.type, AbstractionType):
            arrow_goal = ret_t.type
        if arrow_goal is not None:
            for name, _ in [
                (n, t) for n, t in ctx.concrete_vars() if isinstance(t, AbstractionType) and match_type(t, arrow_goal)
            ]:
                yield Var(name)
            return
        if isinstance(base_t, TypeVar):
            for name, t in ctx.concrete_vars():
                if t == base_t:
                    yield Var(name)
            return
        assert isinstance(base_t, TypeConstructor)
        for name, _ in [
            (n, t) for n, t in ctx.concrete_vars() if isinstance(t, TypeConstructor) and match_type(t, base_t)
        ]:
            yield Var(name)
        match base_t:
            case TypeConstructor(Name("Bool", 0)):
                yield from [Literal(True, base_t), Literal(False, base_t)]
            case TypeConstructor(Name("Int", 0)):
                # ?intLit: solved by z3 against the VC (goal refinement) here.
                yield from _solve_literal(ret_t, base_t)
            case TypeConstructor(Name("Float", 0)):
                # ?floatLit: solved by z3 against the VC (goal refinement) here.
                yield from _solve_literal(ret_t, base_t)
            case TypeConstructor(Name("String", 0)):
                yield from (
                    Literal(s, base_t)
                    for s in ("", " ", "a", "b", "0", "1", "x", "y", "\n", "\t", "true", "false", "[]", "{}", "nil")
                )
            case TypeConstructor(Name("Unit", 0)):
                yield Literal(None, base_t)
            case _:
                raise NotImplementedError
    elif level >= 1:
        arrow_syn: AbstractionType | None = ret_t if isinstance(ret_t, AbstractionType) else None
        if arrow_syn is None and isinstance(ret_t, RefinedType) and isinstance(ret_t.type, AbstractionType):
            arrow_syn = ret_t.type
        if arrow_syn is not None:
            ctx_l = ctx.with_var(arrow_syn.var_name, arrow_syn.var_type)
            for bod in synthes_memory(ctx_l, level - 1, arrow_syn.type, skip, mem):
                lam = Abstraction(arrow_syn.var_name, bod)
                if isinstance(ret_t, RefinedType):
                    yield Annotation(lam, ret_t)
                else:
                    yield lam
        for name, typ in [
            (n, ty) for n, ty in ctx.concrete_vars() if not isinstance(ty, TypeConstructor) and not skip(n)
        ]:
            if isinstance(typ, TypePolymorphism):
                # Synquid APP rule with polymorphic instantiation: instantiate the
                # bound type variables by *unifying the function's return type with
                # the goal* (Polikarpova et al., PLDI'16). Unifying ``List a`` with
                # the goal ``List Enemy`` yields ``a := Enemy``, so the user's own
                # containers get built -- and only the one relevant instantiation
                # is tried (no universe enumeration, no combinatorial blow-up).
                tyvars, inner = _peel_polymorphism(typ)
                params_t, ret_template = _uncurry_arrow(inner)
                # A binding whose return type is a *bare* bound type variable
                # (e.g. ``+`` / ``Array_get`` : ``∀a. … -> a``) unifies with any
                # goal, so it would be instantiated at every user datatype --
                # ``chunk + chunk``, ``level + level`` -- and these nonsensical
                # builders blow up the search combinatorially. Only build such
                # "returns-anything" functions at primitive goals (where they are
                # the actual arithmetic/relational ops); data constructors, whose
                # return head is a concrete type constructor, are unaffected.
                ret_unref = refined_to_unrefined_type(ret_template)
                if isinstance(ret_unref, TypeVar) and ret_unref.name in set(tyvars):
                    goal_base = refined_to_unrefined_type(ret_t)
                    if not (isinstance(goal_base, TypeConstructor) and goal_base.name.name in _NUMERIC_BASES):
                        continue
                sub = _match_type(ret_template, ret_t, set(tyvars))
                if sub is None or any(tv not in sub for tv in tyvars):
                    continue
                head: Term = Var(name)
                for tv in tyvars:
                    head = TypeApplication(head, sub[tv])
                inst_params: list[Type] = []
                for p in params_t:
                    for tv in tyvars:
                        p = type_substitution(p, tv, sub[tv])
                    inst_params.append(p)
                params = [_arg_gen(ctx, level, i, skip, mem) for i in inst_params]
                for combo in itertools.product(*params):
                    term: Term = head
                    for a in combo:
                        term = Application(term, a)
                    yield term
            else:
                if synquid_application_arg_types(typ, ret_t) is None:
                    continue
                params_t, t = uncurry(typ)
                if refined_to_unrefined_type(t) != base_t:
                    continue
                head_tc = _head_result_constructor(t)
                if head_tc is None:
                    continue
                params = [_arg_gen(ctx, level, i, skip, mem) for i in params_t]
                params.insert(0, [Var(name)])
                for i in itertools.product(*params):
                    yield closing(i, head_tc)
        bool_t = TypeConstructor(Name("Bool", 0), [])
        atoms_q = extract_qualifier_atoms(ctx, goal_type=ret_t)
        guard_quads = bool_quad_conjunctions(ctx, atoms_q)
        guard_triples = bool_triple_conjunctions(ctx, atoms_q)
        guard_pairs = bool_pairwise_conjunctions(ctx, atoms_q)
        guard_terms = bool_terms_from_qualifier_atoms(ctx, atoms_q)
        cond = chain(
            iter(guard_quads),
            iter(guard_triples),
            iter(guard_pairs),
            iter(guard_terms),
            synthes_memory(ctx, level - 1, bool_t, skip, mem),
        )
        then = synthes_memory(ctx, level - 1, ret_t, skip, mem)
        otherwise = synthes_memory(ctx, level - 1, ret_t, skip, mem)
        for cand in itertools.product(cond, then, otherwise):
            if isinstance(cand[0], If):
                break
            yield Annotation(If(cand[0], cand[1], cand[2]), ret_t)
