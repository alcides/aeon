from __future__ import annotations

from typing import Any, Generator

from aeon.core.liquid import LiquidApp
from aeon.core.types import LiquidHornApplication
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.core.liquid_ops import liquid_prelude
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import LiquidTypeCheckingContext, check_liquid
from aeon.verification.helpers import constraint_builder
from aeon.verification.helpers import end
from aeon.verification.helpers import imp
from aeon.verification.smt import smt_valid
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.vcs import UninterpretedFunctionDeclaration

Assignment = dict[str, list[LiquidTerm]]


def smt_base_type(ty: Type) -> str | None:
    if isinstance(ty, AbstractionType):
        return None
    if isinstance(ty, BaseType):
        return str(ty)
    elif isinstance(ty, RefinedType):
        return smt_base_type(ty.type)
    else:
        return None


def fresh(context: TypingContext, ty: Type) -> Type:
    if isinstance(ty, BaseType):
        return ty
    elif isinstance(ty, RefinedType) and isinstance(ty.refinement,
                                                    LiquidHornApplication):
        id = context.fresh_var()
        v = f"v_{id}"
        # TODO Poly: check if t should be in LiquidTypes
        return RefinedType(
            v,
            ty.type,
            LiquidHornApplication(f"{id}",
                                  [(LiquidVar(n), t)
                                   for n, t in context.vars() + [(v, ty.type)]
                                   if isinstance(t, BaseType)]),
        )
    elif isinstance(ty, RefinedType):
        return ty
    elif isinstance(ty, AbstractionType):
        sp = fresh(context, ty.var_type)
        tp = fresh(context.with_var(ty.var_name, ty.var_type), ty.type)
        return AbstractionType(ty.var_name, sp, tp)
    elif isinstance(ty, Top):
        return ty
    elif isinstance(ty, TypeVar):
        return ty
    elif isinstance(ty, TypePolymorphism):
        return TypePolymorphism(ty.name, ty.kind, fresh(context, ty.body))
    else:
        assert False, f"Type not freshable: {ty}, {type(ty)}"


def obtain_holes(t: LiquidTerm) -> list[LiquidHornApplication]:
    if isinstance(t, LiquidHornApplication):
        return [t]
    elif (isinstance(t, LiquidLiteralBool) or isinstance(t, LiquidLiteralInt)
          or isinstance(t, LiquidLiteralFloat)
          or isinstance(t, LiquidLiteralString)):
        return []
    elif isinstance(t, LiquidVar):
        return []
    elif isinstance(t, LiquidApp):
        holes: list[LiquidHornApplication] = []
        for h in t.args:
            holes = holes + obtain_holes(h)
        return holes
    else:
        assert False, f"Unkown term type: {t} ({type(t)})"


def obtain_holes_constraint(c: Constraint) -> list[LiquidHornApplication]:
    match c:
        case Conjunction(c1, c2):
            return obtain_holes_constraint(c1) + obtain_holes_constraint(c2)
        case Implication(_, _, pre, post):
            return obtain_holes(pre) + obtain_holes_constraint(post)
        case LiquidConstraint(e):
            return obtain_holes(e)
        case UninterpretedFunctionDeclaration(_, _, post):
            return obtain_holes_constraint(post)
        case _:
            assert False, c


def contains_horn(t: LiquidTerm) -> bool:
    if (isinstance(t, LiquidLiteralInt) or isinstance(t, LiquidLiteralBool)
            or isinstance(t, LiquidLiteralString)
            or isinstance(t, LiquidLiteralFloat)):
        return False
    elif isinstance(t, LiquidVar):
        return False
    elif isinstance(t, LiquidHornApplication):
        return True
    elif isinstance(t, LiquidApp):
        return all([contains_horn(arg) for arg in t.args])
    else:
        assert False


def contains_horn_constraint(c: Constraint) -> bool:
    if isinstance(c, LiquidConstraint):
        return contains_horn(c.expr)
    elif isinstance(c, Conjunction):
        return contains_horn_constraint(c.c1) or contains_horn_constraint(c.c2)
    elif isinstance(c, Implication):
        return contains_horn(c.pred) or contains_horn_constraint(c.seq)
    elif isinstance(c, UninterpretedFunctionDeclaration):
        return contains_horn_constraint(c.seq)
    else:
        assert False


def wellformed_horn(predicate: LiquidTerm) -> bool:
    if not contains_horn(predicate):
        return True
    elif (isinstance(predicate, LiquidApp) and predicate.fun == "&&"
          and not contains_horn(predicate.args[0])
          and isinstance(predicate.args[1], LiquidHornApplication)):
        return True
    elif isinstance(predicate, LiquidHornApplication):
        return True
    else:
        return False


def mk_arg(i: int) -> str:
    return f"_{i}"


def get_possible_args(vars: list[tuple[LiquidTerm, BaseType | TypeVar]],
                      arity: int):
    if arity == 0:
        yield []
    else:
        for base in get_possible_args(vars, arity - 1):
            for i, (_, _) in enumerate(vars):
                yield [LiquidVar(mk_arg(i))] + base
                yield [LiquidLiteralBool(True)] + base
                yield [LiquidLiteralBool(False)] + base
                yield [LiquidLiteralInt(0)] + base
                yield [LiquidLiteralInt(1)] + base


def build_possible_assignment(
        hole: LiquidHornApplication) -> Generator[LiquidApp]:
    ctx = LiquidTypeCheckingContext(
        known_types=[
            BaseType(bn) for bn in ["Unit", "Bool", "Int", "Float", "String"]
        ],
        functions=liquid_prelude,
        variables={
            mk_arg(i): t
            for i, (_, t) in enumerate(hole.argtypes)
        },
    )

    for fname in liquid_prelude:
        ftype = liquid_prelude[fname]
        arity = len(ftype) - 1
        for args in get_possible_args(hole.argtypes, arity):
            # At least one LiquidVar must be used.
            if not any(isinstance(a, LiquidVar) for a in args):
                continue

            app = LiquidApp(fname, list(args))

            if check_liquid(ctx, app, t_bool):
                yield app


def build_initial_assignment(c: Constraint) -> Assignment:
    holes = obtain_holes_constraint(c)
    assign: dict[str, list[LiquidTerm]] = {}
    for h in holes:
        if h.name not in assign:
            assign[h.name] = list(build_possible_assignment(h))
    return assign


def merge_assignments(xs: list[LiquidTerm]) -> LiquidTerm:
    b = LiquidLiteralBool(True)
    for c in xs:
        b = mk_liquid_and(b, c)
    return b


def split(c: Constraint) -> list[Constraint]:
    match c:
        case LiquidConstraint(_):
            return [c]
        case Conjunction(c1, c2):
            return split(c1) + split(c2)
        case Implication(name, base, pre, post):
            return [Implication(name, base, pre, cp) for cp in split(post)]
        case UninterpretedFunctionDeclaration(name, type, seq):
            return [
                UninterpretedFunctionDeclaration(name, type, c)
                for c in split(seq)
            ]
        case _:
            assert False


def build_forall_implication(
    vs: list[tuple[str, Type]],
    p: LiquidTerm,
    c: Constraint,
) -> Constraint:
    if not vs:
        return c
    lastEl = vs[-1]
    assert isinstance(lastEl[1], BaseType)
    cf = Implication(lastEl[0], lastEl[1], p, c)
    for n, t in vs[-2::-1]:
        assert isinstance(t, BaseType)
        cf = Implication(n, t, LiquidLiteralBool(True), cf)
    return cf


def simpl(vs: list[tuple[str, Type]], p: LiquidTerm,
          c: Constraint) -> Constraint:
    if isinstance(c, Implication):
        return simpl(vs + [(c.name, c.base)], mk_liquid_and(p, c.pred), c.seq)
    else:
        return build_forall_implication(vs, p, c)


def flat(c: Constraint) -> list[Constraint]:
    return [simpl([], LiquidLiteralBool(True), cp) for cp in split(c)]


def has_k_head(c: Constraint) -> bool:
    match c:
        case Conjunction(_, _):
            assert False
        case Implication(_, _, _, post):
            return has_k_head(post)
        case LiquidConstraint(e):
            return isinstance(e, LiquidHornApplication)
        case UninterpretedFunctionDeclaration(_, _, post):
            return has_k_head(post)
        case _:
            assert False, f"Unkown constraint type: {c} ({type(c)})"


def apply_constraint(assign: Assignment, c: Constraint) -> Constraint:
    match c:
        case LiquidConstraint(e):
            return LiquidConstraint(apply_liquid(assign, e))
        case Conjunction(c1, c2):
            return Conjunction(
                apply_constraint(assign, c1),
                apply_constraint(assign, c2),
            )
        case Implication(name, base, pre, post):
            return Implication(
                name,
                base,
                apply_liquid(assign, pre),
                apply_constraint(assign, post),
            )
        case UninterpretedFunctionDeclaration(name, base, post):
            return UninterpretedFunctionDeclaration(
                name, base, apply_constraint(assign, post))
        case _:
            assert False


def fill_horn_arguments(h: LiquidHornApplication,
                        candidate: LiquidTerm) -> LiquidTerm:
    for i, (n, _) in enumerate(h.argtypes):
        assert isinstance(n, LiquidTerm)
        candidate = substitution_in_liquid(candidate, n, mk_arg(i))
    return candidate


def apply_liquid(assign: Assignment, c: LiquidTerm) -> LiquidTerm:
    if isinstance(c, LiquidHornApplication):
        if c.name in assign:
            ne = assign[c.name]
            return fill_horn_arguments(c, merge_assignments(ne))
        else:
            return c
    elif isinstance(c, LiquidApp):
        return LiquidApp(c.fun, [apply_liquid(assign, ci) for ci in c.args])
    else:
        return c


def apply(assign: Assignment, c: Any):
    if isinstance(c, Constraint):
        return apply_constraint(assign, c)
    elif isinstance(c, LiquidTerm):
        return apply_liquid(assign, c)
    assert False


def extract_components_of_imp(
    c: Constraint,
) -> tuple[list[tuple[str, BaseType | TypeVar | AbstractionType | Top]], tuple[
        LiquidTerm, LiquidTerm]]:
    match c:
        case UninterpretedFunctionDeclaration(name, base, post):
            (vs1, (p, h)) = extract_components_of_imp(post)
            vsh: list[tuple[str,
                            BaseType | TypeVar | AbstractionType | Top]] = [
                                (name, base)
                            ]
            return (vsh + vs1, (p, h))
        case Implication(name, base, pre, seq):
            (vs1, (p, h)) = extract_components_of_imp(seq)
            vs: list[tuple[str,
                           BaseType | TypeVar | AbstractionType | Top]] = [
                               (name, base)
                           ]
            return (vs + vs1, (mk_liquid_and(pre, p), h))
        case LiquidConstraint(e):
            return ([], (LiquidLiteralBool(True), e))
        case _:
            assert False, f"Unkown context: {c} ({type(c)})"


def weaken(assign, c: Constraint) -> Assignment:
    (vs, (p, h)) = extract_components_of_imp(c)
    assert isinstance(h, LiquidHornApplication)
    assert h.name in assign
    current_rep = assign[h.name]

    def keep(q: LiquidTerm) -> bool:
        assert isinstance(h, LiquidHornApplication)
        qp = fill_horn_arguments(h, q)
        nc = constraint_builder(vs, imp(apply(assign, p), end(qp)))
        return smt_valid(nc)

    qsp = [q for q in current_rep if keep(q)]
    return {k: assign[k] if k != h.name else qsp for k in assign}


def fixpoint(cs: list[Constraint], assign) -> Assignment:
    ncs = [c for c in cs if not smt_valid(apply(assign, c))]
    if not ncs:
        return assign
    else:
        weakened_assignment = weaken(assign, ncs[0])
        return fixpoint(cs, weakened_assignment)


# TODO uninterpreted: We need to pass the context here, to use custom measures in the horn clause.


def solve(c: Constraint) -> bool:
    # Performance improvement
    if not contains_horn_constraint(c):
        # TODO: Try to simplify the expression before sending to the SMT solver
        # v = reduce_to_useful_constraint(c)
        return smt_valid(c)
    cs = flat(c)
    csk = [c for c in cs if has_k_head(c)]
    csp = [c for c in cs if not has_k_head(c)]
    assignment0: Assignment = build_initial_assignment(c)
    subst = fixpoint(csk, assignment0)

    merged_csps: Constraint
    merged_csps = LiquidConstraint(LiquidLiteralBool(True))
    for pi in csp:
        merged_csps = Conjunction(merged_csps, pi)
    c_final: Constraint = apply(subst, merged_csps)
    return smt_valid(c_final)
