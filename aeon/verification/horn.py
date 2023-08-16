from __future__ import annotations

from typing import Any
from typing import Sequence

from aeon.core.liquid import LiquidApp
from aeon.core.liquid import LiquidHornApplication
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import all_ops
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType
from aeon.core.types import BaseType
from aeon.core.types import Bottom
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.liquid import type_infer_liquid
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
        args: list[tuple[LiquidTerm, str]] = []
        for n, t in context.vars() + [(v, ty.type)]:
            stp = smt_base_type(t)
            if stp:
                args.append((LiquidVar(n), stp))
        return RefinedType(v, ty.type, LiquidHornApplication(f"{id}", args))
    elif isinstance(ty, RefinedType):
        return ty
    elif isinstance(ty, AbstractionType):
        sp = fresh(context, ty.var_type)
        tp = fresh(context.with_var(ty.var_name, ty.var_type), ty.type)
        return AbstractionType(ty.var_name, sp, tp)
    elif isinstance(ty, Top):
        return ty
    elif isinstance(ty, Bottom):
        return ty
    elif isinstance(ty, TypeVar):
        return ty
    elif isinstance(ty, TypePolymorphism):
        return TypePolymorphism(ty.name, ty.kind, fresh(context, ty.body))
    else:
        print("Type not freshable:", ty, type(ty))
        assert False


def obtain_holes(t: LiquidTerm) -> list[LiquidHornApplication]:
    if isinstance(t, LiquidHornApplication):
        return [t]
    elif isinstance(t, LiquidLiteralBool) or isinstance(
            t, LiquidLiteralInt) or isinstance(t, LiquidLiteralString):
        return []
    elif isinstance(t, LiquidVar):
        return []
    elif isinstance(t, LiquidApp):
        holes: list[LiquidHornApplication] = []
        for h in t.args:
            holes = holes + obtain_holes(h)
        return holes
    else:
        assert False


def obtain_holes_constraint(c: Constraint) -> list[LiquidHornApplication]:
    if isinstance(c, LiquidConstraint):
        return obtain_holes(c.expr)
    elif isinstance(c, Conjunction):
        return obtain_holes_constraint(c.c1) + obtain_holes_constraint(c.c2)
    elif isinstance(c, Implication):
        return obtain_holes(c.pred) + obtain_holes_constraint(c.seq)
    else:
        assert False


def contains_horn(t: LiquidTerm) -> bool:
    if isinstance(t, LiquidLiteralInt) or isinstance(
            t, LiquidLiteralBool) or isinstance(t, LiquidLiteralString):
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


def get_possible_args(vars: Sequence[tuple[LiquidTerm, str]], arity: int):
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


def reverse_type(t: str) -> Type:
    return {"Int": t_int, "Bool": t_bool}[t]


def build_possible_assignment(hole: LiquidHornApplication):
    ctx: TypingContext = EmptyContext()
    for i, (_, t) in enumerate(hole.argtypes):
        ctx = VariableBinder(ctx, mk_arg(i), reverse_type(t))
    for opn, opt in all_ops:
        arity = len(opt) - 1
        for args in get_possible_args(hole.argtypes, arity):
            if not any([isinstance(a, LiquidVar) for a in args]):
                continue
            app = LiquidApp(opn, list(args))
            if type_infer_liquid(ctx, app) == t_bool:
                yield app


def build_initial_assignment(c: Constraint) -> Assignment:
    holes = obtain_holes_constraint(c)
    print("holes of", c, holes)
    assign: dict[str, list[LiquidTerm]] = {}
    for h in holes:
        assign[h.name] = list(build_possible_assignment(h))
    return assign


def merge_assignments(xs: list[LiquidTerm]) -> LiquidTerm:
    b = LiquidLiteralBool(True)
    for c in xs:
        b = mk_liquid_and(b, c)
    return b


def split(c: Constraint) -> list[Constraint]:
    if isinstance(c, LiquidConstraint):
        return [c]
    elif isinstance(c, Conjunction):
        return split(c.c1) + split(c.c2)
    elif isinstance(c, Implication):
        return [Implication(c.name, c.base, c.pred, cp) for cp in split(c.seq)]
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
    if isinstance(c, Conjunction):
        assert False
    elif isinstance(c, Implication):
        return has_k_head(c.seq)
    elif isinstance(c, LiquidConstraint):
        if isinstance(c.expr, LiquidHornApplication):
            return True
        else:
            return False
    else:
        assert False


def apply_constraint(assign: Assignment, c: Constraint) -> Constraint:
    if isinstance(c, LiquidConstraint):
        return LiquidConstraint(apply_liquid(assign, c.expr))
    elif isinstance(c, Conjunction):
        return Conjunction(
            apply_constraint(assign, c.c1),
            apply_constraint(assign, c.c2),
        )
    elif isinstance(c, Implication):
        return Implication(
            c.name,
            c.base,
            apply_liquid(assign, c.pred),
            apply_constraint(assign, c.seq),
        )
    assert False


def fill_horn_arguments(h: LiquidHornApplication,
                        candidate: LiquidTerm) -> LiquidTerm:
    for i, (n, _) in enumerate(h.argtypes):
        assert isinstance(n, LiquidTerm)
        candidate = substitution_in_liquid(candidate, n, mk_arg(i))
    return candidate


def apply_liquid(assign: Assignment, c: LiquidTerm) -> LiquidTerm:
    if isinstance(c, LiquidHornApplication):
        assert c.name in assign
        ne = assign[c.name]
        return fill_horn_arguments(c, merge_assignments(ne))
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
) -> tuple[list[tuple[str, Type]], tuple[LiquidTerm, LiquidTerm]]:
    assert isinstance(c, Implication)
    if isinstance(c.seq, LiquidConstraint):
        vs: list[tuple[str, Type]] = [(c.name, c.base)]
        p = c.pred
        h = c.seq.expr
        return (vs, (p, h))
    elif isinstance(c.seq, Implication):
        (vs1, (p, h)) = extract_components_of_imp(c.seq)
        vsh = [(c.name, c.base)]
        return (vsh + vs1, (p, h))
    else:
        assert False


def weaken(assign, c: Constraint) -> Assignment:
    (vs, (p, h)) = extract_components_of_imp(c)

    # TODO: double check this assert
    assert isinstance(h, LiquidHornApplication)
    assert h.name in assign
    current_rep = assign[h.name]

    def keep(q: LiquidTerm) -> bool:
        # TODO: double check this assert
        assert isinstance(h, LiquidHornApplication)
        qp = fill_horn_arguments(h, q)
        nc = constraint_builder(vs, imp(apply(assign, p), end(qp)))
        return smt_valid(nc)

    qsp = [q for q in current_rep if keep(q)]
    return {h.name: qsp}


def fixpoint(cs: list[Constraint], assign) -> Assignment:
    ncs = [c for c in cs if not smt_valid(apply(assign, c))]
    if not ncs:
        return assign
    else:
        return fixpoint(cs, weaken(assign, ncs[0]))


def solve(c: Constraint) -> bool:
    # Performance improvement
    if not contains_horn_constraint(c):
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
    v = apply(subst, merged_csps)
    print("validate", v, smt_valid(v))
    print("Note: I am debugging here. It seesm that this is false -> true")
    return smt_valid(v)
