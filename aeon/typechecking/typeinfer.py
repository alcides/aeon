from __future__ import annotations
from dataclasses import replace
from typing import Iterable

from loguru import logger

import aeon.logger.logger  # noqa: F401  — registers custom levels (SYNTH_TYPE etc.) at import.

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidTerm, liquid_free_vars
from aeon.core.types import LiquidHornApplication, RefinementPolymorphism
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidLiteralString
from aeon.core.liquid import LiquidLiteralUnit
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import ops
from aeon.core.substitutions import (
    instantiate_refinement_in_type,
    instantiate_refinement_with_horn_in_type,
    liquefy,
    substitution_in_liquid,
    substitute_vartype,
    substitution_liquid_in_term,
    substitution_liquid_in_type,
)
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction, RefinementAbstraction, RefinementApplication
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import ImplicitRefinementHole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Kind, is_bare
from aeon.core.types import ExistentialType, with_binders
from aeon.core.types import TypeConstructor
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_string
from aeon.core.types import t_set
from aeon.core.types import t_unit
from aeon.core.types import top
from aeon.core.types import type_free_term_vars
from aeon.facade.api import (
    AeonError,
    CoreInvalidApplicationError,
    CoreSubtypingError,
    CoreTypeApplicationRequiresBareTypesError,
    CoreTypeCheckingError,
    CoreVariableNotInContext,
    CoreWellformnessError,
    CoreWrongKindInTypeApplicationError,
    LiquidTypeCheckingFailedRelation,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment, entailment_context
from aeon.typechecking.termination import termination_metric_constraints
from aeon.typechecking.qualifiers import extract_qualifier_atoms
from aeon.typechecking.well_formed import wellformed
from aeon.verification.horn import fresh
from aeon.verification.sub import ensure_refined
from aeon.verification.sub import implication_constraint
from aeon.verification.sub import is_first_order_function
from aeon.verification.sub import sub
from aeon.verification.vcs import Conjunction, UninterpretedFunctionDeclaration
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import LiquidConstraint
from aeon.verification.horn import solve
from aeon.utils.location import Location
from aeon.utils.name import Name, fresh_counter
from aeon.verification.helpers import (
    constraint_location,
    remove_unrelated_context,
    simplify_constraint,
    conjunctive_normal_form,
    is_implication_true,
    split_or_in_conclusion,
)

ctrue = LiquidConstraint(LiquidLiteralBool(True))


def _and(a: LiquidTerm, b: "LiquidTerm | None") -> LiquidTerm:
    """``a && b`` when ``b`` is present, otherwise just ``a``."""
    if b is None:
        return a
    return LiquidApp(Name("&&", 0), [a, b])


def _strip_type_level_wrappers(t: Term) -> Term:
    while isinstance(t, TypeAbstraction) or isinstance(t, RefinementAbstraction) or isinstance(t, Annotation):
        if isinstance(t, TypeAbstraction):
            t = t.body
        elif isinstance(t, RefinementAbstraction):
            t = t.body
        else:
            t = t.expr
    return t


def _erase_return_refinement(ty: Type) -> Type:
    """Weaken ``ty``'s final codomain to its bare carrier type.

    Walks the function-type spine (type/refinement polymorphism and arrow
    binders) down to the return type; if that return type is a ``RefinedType``,
    drop the refinement, keeping only the underlying ``TypeConstructor``/
    ``TypeVar``.

    Used to weaken the *inductive hypothesis* of a recursive binding that has no
    well-founded termination metric. Typing a recursive call at the declared
    refined return type is only sound when the function provably terminates;
    without a metric, a non-terminating definition could otherwise "prove" an
    absurd codomain such as ``{r:Int | r > r}`` and poison downstream proofs.
    Argument refinements are left intact — they constrain how the function is
    *called*, not what it may *assume* about its own result.
    """
    if isinstance(ty, TypePolymorphism):
        return replace(ty, body=_erase_return_refinement(ty.body))
    if isinstance(ty, RefinementPolymorphism):
        return replace(ty, body=_erase_return_refinement(ty.body))
    if isinstance(ty, AbstractionType):
        return replace(ty, type=_erase_return_refinement(ty.type))
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


_TRUSTED_NATIVE_HEADS = frozenset({"native", "native_import", "uninterpreted"})


def _is_trusted_native_value(t: Term) -> bool:
    """Whether a binding's value is a ``native``/``uninterpreted`` builtin.

    Such a definition is *trusted*: its declared type is an axiom (no body is
    checked), so the return refinement may be assumed at every call site
    (issue #378). Peels the abstraction/annotation wrappers a def body carries,
    then the application/type-application spine down to the head variable.
    """
    while True:
        match t:
            case Abstraction(_, body, _) | TypeAbstraction(_, _, body, _) | RefinementAbstraction(_, _, body, _):
                t = body
            case Annotation(expr, _, _):
                t = expr
            case _:
                break
    while True:
        match t:
            case Application(fun, _, _):
                t = fun
            case TypeApplication(body, _, _) | RefinementApplication(body, _, _):
                t = body
            case _:
                break
    return isinstance(t, Var) and t.name.name in _TRUSTED_NATIVE_HEADS


def _reflected_impl_for(
    name: Name,
    ty: Type,
    impl: Term,
    *,
    has_termination_metric: bool = False,
) -> tuple[tuple[Name, ...], LiquidTerm] | None:
    def has_horn(t: LiquidTerm) -> bool:
        if isinstance(t, LiquidHornApplication):
            return True
        if isinstance(t, LiquidApp):
            return any(has_horn(a) for a in t.args)
        return False

    if not isinstance(ty, AbstractionType):
        if not isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            return None
    if not isinstance(impl, Term):
        return None
    current = _strip_type_level_wrappers(impl)
    impl_params: list[Name] = []
    while isinstance(current, Abstraction):
        impl_params.append(current.var_name)
        current = current.body
    if not impl_params:
        return None
    ty_params: list[Name] = []
    cur_ty: Type = ty
    refinement_params: set[Name] = set()
    while isinstance(cur_ty, TypePolymorphism) or isinstance(cur_ty, RefinementPolymorphism):
        if isinstance(cur_ty, TypePolymorphism):
            cur_ty = cur_ty.body
        else:
            refinement_params.add(cur_ty.name)
            cur_ty = cur_ty.body
    while isinstance(cur_ty, AbstractionType):
        ty_params.append(cur_ty.var_name)
        cur_ty = cur_ty.type
    if len(ty_params) != len(impl_params):
        return None
    liq = liquefy(current)
    if liq is None:
        return None
    if has_horn(liq):
        return None
    for src, dst in zip(impl_params, ty_params):
        if src != dst:
            liq = substitution_in_liquid(liq, LiquidVar(dst), src)
    if any(v.name in {"native", "native_import"} for v in liquid_free_vars(liq)):
        return None
    allowed = set(ty_params) | {name}
    op_names = {op.name for op in ops}
    if any(v not in allowed and v.name not in op_names for v in liquid_free_vars(liq)):
        return None
    is_recursive_body = any(v == name for v in liquid_free_vars(liq))
    if is_recursive_body and not has_termination_metric:
        # Recursive reflection is only enabled when we have explicit termination evidence.
        return None
    if any(v in refinement_params for v in liquid_free_vars(liq)):
        # Current reflection pipeline only supports refinement-polymorphic functions
        # whose runtime body is independent of the refinement predicate symbol.
        return None
    return (tuple(ty_params), liq)


def _selfification_liquid(ctx: TypingContext, t: Term) -> LiquidTerm | None:
    """Liquid encoding of an application term for selfification (issue #378).

    Returns the ``LiquidTerm`` for ``t`` when the whole term is expressible in
    the liquid fragment and every applied symbol will exist on the SMT side:
    a primitive operator, or a context-bound function that
    ``implication_constraint`` / ``entailment_context`` declares (first-order,
    and for polymorphic functions, with a concrete base result). Otherwise
    ``None`` — the caller simply skips selfification.

    Note: encoding an application as an SMT function term identifies
    syntactically equal calls (congruence). This is the purity assumption the
    liquid fragment already makes everywhere applications appear in
    refinements and termination metrics; selfification adds no new trust.
    """
    liq = liquefy(t)
    if liq is None:
        return None
    if any(v.name in {"native", "native_import", "uninterpreted"} for v in liquid_free_vars(liq)):
        return None

    op_names = {op.name for op in ops} | {"ite"}

    def heads_declarable(lt: LiquidTerm) -> bool:
        match lt:
            case LiquidHornApplication():
                return False
            case LiquidApp(fun, args):
                if fun.name not in op_names:
                    # Only monomorphic first-order functions are reliably
                    # declared on the SMT side (``implication_constraint`` for
                    # let-chain binders, ``entailment_context`` for prelude
                    # entries — the latter skips polymorphic binders entirely).
                    fun_ty = ctx.type_of(fun)
                    if not (isinstance(fun_ty, AbstractionType) and is_first_order_function(fun_ty)):
                        return False
                return all(heads_declarable(a) for a in args)
            case LiquidVar(name):
                # A leaf variable is only safe to embed if it will be declared
                # on the SMT side. Both ``implication_constraint`` (let-chain
                # binders) and ``entailment_context`` (context binders) declare
                # value binders of base/refined type but *skip polymorphic
                # binders* — notably nullary inductive constructor constants such
                # as ``List_nil : forall a. {l: List a | len l = 0}``. Embedding
                # one would leave it undeclared in Z3 (a ``KeyError`` at
                # translation time), so bail out of this optional selfification.
                var_ty = ctx.type_of(name)
                if isinstance(var_ty, (TypePolymorphism, RefinementPolymorphism)):
                    return False
                return True
            case _:
                return True

    if not heads_declarable(liq):
        return None
    return liq


def _selfify_application_type(ctx: TypingContext, t: Term, ty: Type) -> Type:
    """Strengthen an application's synthesised type with ``v == ⟦t⟧``.

    Only fires when the result type carries no information of its own — a bare
    base type or a trivially-refined one. Refined codomains (primitive
    operators, refined natives) already state their contract; adding the
    equality there would only grow VCs. This is what lets facts proved about
    the *application term* (e.g. an instantiated axiom about ``fdiv n 10``)
    reach obligations phrased about its *result* (issue #378).
    """

    def selfifiable_base(base: Type) -> bool:
        # Non-parametric constructors only: scalars (Int, Float, Bool, String)
        # and opaque user types map to one SMT sort each. Unit carries no
        # information, and parametric constructors go through per-instantiation
        # sort mangling that selfification should not interfere with.
        return isinstance(base, TypeConstructor) and not base.args and base.name.name != "Unit"

    match ty:
        case TypeConstructor(_, _) if selfifiable_base(ty):
            liq = _selfification_liquid(ctx, t)
            if liq is None:
                return ty
            v = Name("_self", fresh_counter.fresh())
            return RefinedType(v, ty, LiquidApp(Name("==", 0), [LiquidVar(v), liq]))
        case RefinedType(name, base, LiquidLiteralBool(True)) if selfifiable_base(base):
            liq = _selfification_liquid(ctx, t)
            if liq is None:
                return ty
            return RefinedType(name, base, LiquidApp(Name("==", 0), [LiquidVar(name), liq]))
        case _:
            return ty


def is_compatible(a: Kind, b: Kind):
    """Returns whether kind a is a subkind of kind b"""
    return (a == b) or b == Kind.STAR


def argument_is_typevar(ty: Type):
    return (
        isinstance(ty, TypeVar)
        or isinstance(
            ty,
            RefinedType,
        )
        and isinstance(ty.type, TypeVar)
    )


def prim_litbool(t: bool) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    if t:
        return RefinedType(vname, t_bool, LiquidVar(vname))
    else:
        return RefinedType(vname, t_bool, LiquidApp(Name("!", 0), [LiquidVar(vname)]))


def prim_litunit() -> RefinedType:
    """Type of the Unit literal ``()``.

    Unit has a single inhabitant, so the refinement pins ``v`` to the
    sole ``LiquidLiteralUnit`` value. The SMT layer maps ``Unit`` to a
    dedicated sort (see ``aeon.verification.smt.get_sort``) rather than
    re-using ``Bool``.
    """
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        t_unit,
        LiquidApp(Name("==", 0), [LiquidVar(vname), LiquidLiteralUnit()]),
    )


def prim_litint(t: int) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        t_int,
        LiquidApp(Name("==", 0), [LiquidVar(vname), LiquidLiteralInt(t)]),
    )


def prim_litfloat(t: float) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        t_float,
        LiquidApp(Name("==", 0), [LiquidVar(vname), LiquidLiteralFloat(t)]),
    )


def prim_litstring(t: str) -> RefinedType:
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        t_string,
        LiquidApp(Name("==", 0), [LiquidVar(vname), LiquidLiteralString(t)]),
    )


def nonzero_refined(ty: TypeConstructor | TypeVar) -> RefinedType:
    """Wraps ``ty`` in the refinement ``{v : ty | v != 0}``.

    Used for the divisor parameter of ``/`` and ``%`` so that division by a
    statically-zero value is rejected at typechecking. The literal ``0`` is an
    ``Int``; when ``ty`` is ``Float`` (or a base type variable instantiated to
    it) Z3 coerces the numeral into its sort, so the same refinement discharges
    for both ``Int`` and ``Float`` divisors (see the Int/Float coercion in
    ``aeon.typechecking.liquid._unify``)."""
    vname = Name("v", fresh_counter.fresh())
    return RefinedType(
        vname,
        ty,
        LiquidApp(Name("!=", 0), [LiquidVar(vname), LiquidLiteralInt(0)]),
    )


def make_binary_app_type(
    t: Name,
    ity: TypeConstructor | TypeVar,
    oty: TypeConstructor | TypeVar,
    nonzero_divisor: bool = False,
) -> Type:
    """Creates the type of a binary operator.

    When ``nonzero_divisor`` is set, the second parameter (the divisor) carries
    a ``v != 0`` refinement so division/modulo by a statically-zero value is
    rejected."""
    xname = Name("x", fresh_counter.fresh())
    yname = Name("y", fresh_counter.fresh())
    zname = Name("z", fresh_counter.fresh())
    yty: Type = nonzero_refined(ity) if nonzero_divisor else ity
    output = RefinedType(
        zname,
        oty,
        LiquidApp(
            Name("==", 0),
            [
                LiquidVar(zname),
                LiquidApp(
                    t,
                    [LiquidVar(xname), LiquidVar(yname)],
                ),
            ],
        ),
    )
    appt2 = AbstractionType(yname, yty, output)
    appt1 = AbstractionType(xname, ity, appt2)
    return appt1


def prim_op(t: Name) -> Type:
    match t.name:
        case "%":
            return make_binary_app_type(t, t_int, t_int, nonzero_divisor=True)
        case "+" | "-" | "*" | "/":
            name_a = Name("a", fresh_counter.fresh())
            return TypePolymorphism(
                name_a,
                Kind.BASE,
                make_binary_app_type(t, TypeVar(name_a), TypeVar(name_a), nonzero_divisor=t.name == "/"),
            )
        case "==" | "!=" | ">" | ">=" | "<" | "<=":
            name_a = Name("a", fresh_counter.fresh())
            return TypePolymorphism(name_a, Kind.BASE, make_binary_app_type(t, TypeVar(name_a), t_bool))
        case "&&" | "||":
            return make_binary_app_type(t, t_bool, t_bool)
        case "!":
            name = Name("fresh", fresh_counter.fresh())
            return AbstractionType(name, t_bool, t_bool)
        case "-->":
            return make_binary_app_type(t, t_bool, t_bool)
        case "Set_sng":
            name = Name("fresh", fresh_counter.fresh())
            return AbstractionType(name, t_int, t_set)
        case "Set_cup" | "Set_cap" | "Set_dif":
            return make_binary_app_type(t, t_set, t_set)
        case "Set_mem":
            xname = Name("x", fresh_counter.fresh())
            sname = Name("s", fresh_counter.fresh())
            return AbstractionType(xname, t_int, AbstractionType(sname, t_set, t_bool))
        case "Set_sub":
            return make_binary_app_type(t, t_set, t_bool)
        case _:
            assert False, f"Unknown selfication of {t}"


def rename_liquid_term(refinement: LiquidTerm, old_name: Name, new_name: Name):
    if isinstance(refinement, LiquidVar):
        if refinement.name == old_name:
            return LiquidVar(new_name)
        else:
            return refinement
    elif isinstance(refinement, LiquidLiteralBool):
        return refinement
    elif isinstance(refinement, LiquidLiteralInt):
        return refinement
    elif isinstance(refinement, LiquidLiteralFloat):
        return refinement
    elif isinstance(refinement, LiquidApp):
        return LiquidApp(
            refinement.fun,
            [rename_liquid_term(x, old_name, new_name) for x in refinement.args],
        )
    elif isinstance(refinement, LiquidHornApplication):
        if refinement.name == old_name:
            return LiquidHornApplication(
                new_name,
                [(rename_liquid_term(x, old_name, new_name), t) for (x, t) in refinement.argtypes],
            )
        else:
            return LiquidHornApplication(
                refinement.name,
                [(rename_liquid_term(x, old_name, new_name), t) for (x, t) in refinement.argtypes],
            )
    else:
        assert False


def renamed_refined_type(ty: RefinedType) -> RefinedType:
    old_name = ty.name
    new_name = Name("_inner_" + old_name.name, fresh_counter.fresh())

    refinement = rename_liquid_term(ty.refinement, old_name, new_name)
    return RefinedType(new_name, ty.type, refinement)


def _as_predicate_type(sort: Type) -> AbstractionType:
    """The full predicate type of an abstract-refinement sort.

    Refinement sorts now carry the full (possibly n-ary) predicate type
    ``d1 -> ... -> Bool``. Legacy callers (and a few unit tests that build core
    nodes directly) may still pass a bare domain ``d``, which is wrapped as
    ``d -> Bool`` so downstream code always sees an ``AbstractionType``.
    """
    if isinstance(sort, AbstractionType):
        return sort
    return AbstractionType(Name("_", fresh_counter.fresh()), sort, t_bool)


def synth(ctx: TypingContext, t: Term) -> tuple[Constraint, Type]:
    match t:
        case Literal(_, TypeConstructor(Name("Unit", _))):
            return (ctrue, prim_litunit())
        case Literal(vb, TypeConstructor(Name("Bool", _))):
            assert isinstance(vb, bool)
            return (ctrue, prim_litbool(vb))
        case Literal(vi, TypeConstructor(Name("Int", _))):
            assert isinstance(vi, int)
            return (ctrue, prim_litint(vi))
        case Literal(vf, TypeConstructor(Name("Float", _))):
            assert isinstance(vf, float)
            return (ctrue, prim_litfloat(vf))
        case Literal(vs, TypeConstructor(Name("String", _))):
            assert isinstance(vs, str)
            return (ctrue, prim_litstring(vs))
        case Var(name):
            if name in ops:
                return (ctrue, prim_op(name))
            ty = ctx.type_of(name)
            if not ty:
                raise CoreVariableNotInContext(ctx, t)
            if isinstance(ty, TypeConstructor) or isinstance(ty, RefinedType) or isinstance(ty, TypeVar):
                ty = ensure_refined(ty)
                assert isinstance(ty, RefinedType)
                if ty.name == t.name:
                    ty = renamed_refined_type(ty)
                ty = RefinedType(
                    ty.name,
                    ty.type,
                    LiquidApp(
                        Name("&&", 0),
                        [
                            ty.refinement,
                            LiquidApp(
                                Name("==", 0),
                                [
                                    LiquidVar(ty.name),
                                    LiquidVar(t.name),
                                ],
                            ),
                        ],
                    ),
                )
            return (ctrue, ty)
        case Application(fun, arg):
            (c, ty) = synth(ctx, fun)
            # Lift any binders from the function's type to the outer scope so
            # the body underneath can be matched as an AbstractionType.
            fun_binders: tuple[tuple[Name, Type], ...] = ()
            if isinstance(ty, ExistentialType):
                fun_binders = ty.binders
                ty = ty.body
            # Binders just lifted from the function's type are in scope for
            # the argument check and any inner synth: atype may reference
            # them (e.g. dependent parameter types like {t:Float | t >= y}).
            ctx_inner = ctx
            for bn, bt in fun_binders:
                ctx_inner = ctx_inner.with_var(bn, bt)
            match ty:
                case AbstractionType(aname, atype, rtype):
                    outer_binders: tuple[tuple[Name, Type], ...] = fun_binders
                    cp = check(ctx_inner, arg, atype)
                    # Abstractions can't be synthesised on their own (no
                    # annotation), and Var/Literal liquefy directly. In all
                    # three cases the existing direct substitution path is
                    # what we want — the type system either preserves the
                    # equation (Var, Literal, liquefiable App) or silently
                    # passes the body through (Abstraction).
                    if isinstance(arg, (Var, Literal, Abstraction)):
                        t_subs = substitution_in_type(rtype, arg, aname)
                    else:
                        # Form B existential introduction: synth the argument
                        # to get its most precise type, prepend a fresh
                        # binder carrying its refinement, and substitute the
                        # binder name into the result type. Any binders
                        # already on the argument's type lift to the outer
                        # scope (binders are always flat).
                        #
                        # A bare Hole has no synthesisable type (synth defaults
                        # it to a polymorphic type variable), which is not an SMT
                        # base type and would leave the `_y` binder undeclared in
                        # the solver. But the hole was just `check`ed against the
                        # domain type `atype`, so that is its type here — use it
                        # so a hole in argument position needs no annotation.
                        if isinstance(arg, Hole):
                            ty_arg = atype
                        else:
                            (_, ty_arg) = synth(ctx_inner, arg)
                        if isinstance(ty_arg, ExistentialType):
                            outer_binders = outer_binders + ty_arg.binders
                            ty_arg = ty_arg.body
                        y = Name("_y", fresh_counter.fresh())
                        binder_ty = ensure_refined(ty_arg)
                        if isinstance(binder_ty, RefinedType):
                            renamed = substitution_in_liquid(binder_ty.refinement, LiquidVar(y), binder_ty.name)
                            assert isinstance(binder_ty.type, (TypeConstructor, TypeVar))
                            binder_ty = RefinedType(y, binder_ty.type, renamed)
                        outer_binders = outer_binders + ((y, binder_ty),)
                        t_subs = substitution_in_type(rtype, Var(y), aname)
                    # cp may reference the function's lifted binders through
                    # atype; wrap c0 in implications over them so those
                    # references are bound when the constraint reaches SMT.
                    # Argument-side binders propagate to the caller via the
                    # existential type and get their implication wrap there
                    # (e.g. in Let's opened_binders loop).
                    c0: Constraint = Conjunction(c, cp)
                    for bn, bt in reversed(fun_binders):
                        c0 = implication_constraint(bn, bt, c0, t.loc)
                    # Selfify uninformative result types so the value stays
                    # connected to the call that produced it (issue #378).
                    t_subs = _selfify_application_type(ctx_inner, t, t_subs)
                    return (c0, with_binders(outer_binders, t_subs))
                case _:
                    raise CoreInvalidApplicationError(t, ty)
        case Let(var_name, var_value, body):
            (c1, t1) = synth(ctx, var_value)
            # Form B elimination: if the value's type carries existential binders,
            # open them into the surrounding scope (each binder name becomes a
            # context entry under its refinement) and let the body see the
            # bare body type.
            opened_binders: tuple[tuple[Name, Type], ...] = ()
            if isinstance(t1, ExistentialType):
                opened_binders = t1.binders
                t1 = t1.body
            nctx: TypingContext = ctx
            for bn, bt in opened_binders:
                nctx = nctx.with_var(bn, bt)
            nctx = nctx.with_var(var_name, t1)
            (c2, t2) = synth(nctx, body)
            term_vars = type_free_term_vars(t1)
            assert t.var_name not in term_vars
            reflected_impl = _reflected_impl_for(var_name, t1, var_value)
            inner = implication_constraint(var_name, t1, c2, body.loc, reflected_impl=reflected_impl)
            for bn, bt in reversed(opened_binders):
                inner = implication_constraint(bn, bt, inner, body.loc)
            # Form B introduction: if the body's type still mentions a name
            # bound here (`var_name` or any of the opened binders), wrap it
            # in an existential so the scope leak is preserved as a binder
            # rather than as a free variable when the type flows outward.
            t2_free = type_free_term_vars(t2)
            leaking: list[tuple[Name, Type]] = []
            for bn, bt in opened_binders:
                if bn in t2_free:
                    leaking.append((bn, bt))
            if var_name in t2_free:
                leaking.append((var_name, t1))
            if leaking:
                t2 = with_binders(tuple(leaking), t2)
            r = (Conjunction(c1, inner), t2)
            return r
        case Rec(var_name, var_type, var_value, body):
            has_metric = bool(t.decreasing_by)
            # For a ``mutual`` group the inductive hypothesis (assuming the
            # declared, refined types of self *and* siblings while checking the
            # value) is only sound when the *whole* group is well-founded — every
            # member must carry a termination metric, since one member's
            # termination depends on its callees terminating too.
            group_has_metric = has_metric and all(bool(c.decreasing_by) for c in t.companions)
            # The recursive occurrence may assume the declared (refined) return
            # type as an inductive hypothesis only when a well-founded
            # termination metric justifies the induction. Without one, weaken
            # the hypothesis to the bare codomain so a non-terminating
            # definition cannot "prove" an absurd refinement (see
            # recursion_soundness_test.py). Non-recursive bindings are
            # unaffected: their body never references var_name, so the weaker
            # context binding is never consulted.
            rec_var_type = var_type if group_has_metric else _erase_return_refinement(var_type)
            rec_ctx: TypingContext = ctx.with_var(var_name, rec_var_type)
            # Bring mutually-recursive siblings into scope for the value, under
            # the same soundness gating.
            for comp in t.companions:
                comp_type = comp.type if group_has_metric else _erase_return_refinement(comp.type)
                rec_ctx = rec_ctx.with_var(comp.name, comp_type)
            c1 = check(rec_ctx, var_value, var_type)
            nrctx: TypingContext = ctx.with_var(var_name, var_type)
            # Termination obligations (including cross-function calls within the
            # group) are synthesised under a context that knows the siblings.
            term_ctx: TypingContext = nrctx
            for comp in t.companions:
                term_ctx = term_ctx.with_var(comp.name, comp.type)
            (c2, t2) = synth(nrctx, body)
            reflected_impl = _reflected_impl_for(
                var_name,
                var_type,
                var_value,
                has_termination_metric=has_metric,
            )
            keep_refs = _is_trusted_native_value(var_value)
            c1 = implication_constraint(
                var_name, var_type, c1, var_value.loc, reflected_impl=reflected_impl, keep_refinements=keep_refs
            )
            c2 = implication_constraint(
                var_name, var_type, c2, body.loc, reflected_impl=reflected_impl, keep_refinements=keep_refs
            )
            term_c = termination_metric_constraints(t, term_ctx)
            term_c = implication_constraint(
                var_name, var_type, term_c, var_value.loc, reflected_impl=reflected_impl, keep_refinements=keep_refs
            )
            # Declare mutually-recursive siblings so calls to them inside this
            # member's value (e.g. selfified applications ``v == odd (n - 1)``)
            # translate. When the whole group is well-founded and a sibling's
            # body reflects (it doesn't itself call another sibling), reflect its
            # definition so relational refinements like ``{r | g r = x}`` can use
            # it; otherwise declare it uninterpreted.
            for comp in t.companions:
                comp_reflected = (
                    _reflected_impl_for(comp.name, comp.type, comp.value, has_termination_metric=group_has_metric)
                    if (group_has_metric and comp.value is not None)
                    else None
                )
                comp_keep = comp.value is not None and _is_trusted_native_value(comp.value)
                c1 = implication_constraint(
                    comp.name, comp.type, c1, var_value.loc, reflected_impl=comp_reflected, keep_refinements=comp_keep
                )
            # Form B introduction: if the body's type still mentions `var_name`,
            # wrap it in an existential so the scope leak is preserved as a
            # binder when the type flows outward.
            if var_name in type_free_term_vars(t2):
                t2 = with_binders(((var_name, var_type),), t2)
            return Conjunction(Conjunction(c1, c2), term_c), t2
        case Annotation(expr, ty):
            nty = fresh(ctx, ty)
            c = check(ctx, expr, nty)
            return c, nty
        case TypeApplication(body, ty):
            if not is_bare(ty):
                # Type Application only works on bare types.
                raise CoreTypeApplicationRequiresBareTypesError(t, ty)
            (c, tabs) = synth(ctx, body)
            nty = fresh(ctx, ty)
            k = ctx.kind_of(nty)
            if isinstance(nty, RefinedType) and isinstance(nty.refinement, LiquidHornApplication):
                nty = nty.type
                k = ctx.kind_of(nty)
            if isinstance(tabs, TypePolymorphism):
                s = type_substitution(tabs.body, tabs.name, nty)
                if k is None or not is_compatible(k, tabs.kind):
                    raise CoreWrongKindInTypeApplicationError(term=t, type=nty, expected_kind=tabs.kind, actual_kind=k)
                return (c, s)
            else:
                if not isinstance(tabs, AbstractionType):
                    raise CoreInvalidApplicationError(t, tabs)
                return (c, tabs)

        case RefinementApplication(body, refinement):
            (c, rp) = synth(ctx, body)
            if not isinstance(rp, RefinementPolymorphism):
                raise CoreInvalidApplicationError(t, rp)
            if isinstance(refinement, ImplicitRefinementHole):
                horn_name = Name("kappa", fresh_counter.fresh())
                nty = instantiate_refinement_with_horn_in_type(rp.body, rp.name, rp.sort, horn_name)
                return (c, nty)
            assert isinstance(refinement, Abstraction)
            # ``rp.sort`` is the full (possibly n-ary) predicate type.
            pred_type = rp.sort
            c_ref = check(ctx, refinement, pred_type)
            nty = instantiate_refinement_in_type(rp.body, rp.name, refinement)
            return (Conjunction(c, c_ref), nty)

        case RefinementAbstraction(pname, psort, inner):
            # Synth-mode Λρ: mirror Chk-RAbs (lines 505-512) but without an expected type.
            # Introduce fκ : psort -> bool, synth the body, wrap the resulting type with
            # RefinementPolymorphism and gate the constraint behind the UF declaration.
            # ``psort`` is the full (possibly n-ary) predicate type.
            fk_type = _as_predicate_type(psort)
            ctx_ext = ctx.with_var(pname, fk_type)
            (c_body, body_ty) = synth(ctx_ext, inner)
            return (
                UninterpretedFunctionDeclaration(pname, fk_type, c_body),
                RefinementPolymorphism(pname, psort, body_ty),
            )

        case If(cond, then, otherwise):
            # Synth-mode If: mirror check-mode (lines 472-493), but the branches don't
            # share an expected type — synth each under its guard and join refinements.
            liq_cond = liquefy(cond)
            assert liq_cond is not None, f"Could not liquefy if-condition {cond}"
            # Synth the cond so its return refinement is propagated into
            # the branches' hypotheses (see check-mode for details).
            (c_synth_cond, t_cond) = synth(ctx, cond)
            ex_binders: tuple[tuple[Name, Type], ...] = ()
            if isinstance(t_cond, ExistentialType):
                ex_binders = t_cond.binders
                t_cond = t_cond.body
            c_sub_cond = sub(ctx, t_cond, t_bool, cond.loc)
            c_cond = Conjunction(c_synth_cond, c_sub_cond)
            branch_ctx = ctx
            for bn, bt in ex_binders:
                branch_ctx = branch_ctx.with_var(bn, bt)
            cond_ref: "LiquidTerm | None" = None
            t_cond_r = ensure_refined(t_cond)
            if isinstance(t_cond_r, RefinedType) and not (
                isinstance(t_cond_r.refinement, LiquidLiteralBool) and t_cond_r.refinement.value is True
            ):
                cond_ref = substitution_in_liquid(t_cond_r.refinement, liq_cond, t_cond_r.name)

            y = Name("_cond", fresh_counter.fresh())
            (c1_inner, t1) = synth(branch_ctx, then)
            c1 = implication_constraint(
                y,
                RefinedType(Name("branch_pos", fresh_counter.fresh()), t_int, _and(liq_cond, cond_ref)),
                c1_inner,
                then.loc,
            )
            (c2_inner, t2) = synth(branch_ctx, otherwise)
            c2 = implication_constraint(
                y,
                RefinedType(
                    Name("branch_neg", fresh_counter.fresh()),
                    t_int,
                    _and(LiquidApp(Name("!", 0), [liq_cond]), cond_ref),
                ),
                c2_inner,
                otherwise.loc,
            )

            t1_r = ensure_refined(t1)
            t2_r = ensure_refined(t2)
            if isinstance(t1_r, RefinedType) and isinstance(t2_r, RefinedType) and t1_r.type == t2_r.type:
                v = Name("v_if", fresh_counter.fresh())
                r1 = substitution_in_liquid(t1_r.refinement, LiquidVar(v), t1_r.name)
                r2 = substitution_in_liquid(t2_r.refinement, LiquidVar(v), t2_r.name)
                joined: Type = RefinedType(
                    v,
                    t1_r.type,
                    LiquidApp(
                        Name("&&", 0),
                        [
                            LiquidApp(Name("-->", 0), [liq_cond, r1]),
                            LiquidApp(Name("-->", 0), [LiquidApp(Name("!", 0), [liq_cond]), r2]),
                        ],
                    ),
                )
            elif t1 == t2:
                # Same non-refinable type (e.g., function type) on both branches.
                joined = t1
            else:
                raise CoreSubtypingError(ctx, t, t1, t2)
            if_constraint: Constraint = Conjunction(c_cond, Conjunction(c1, c2))
            for bn, bt in reversed(ex_binders):
                if_constraint = implication_constraint(bn, bt, if_constraint, t.loc)
            return (if_constraint, joined)

        case Hole(hole_name):
            name_a = Name(hole_name.name, fresh_counter.fresh())
            # Conservative default: treat the hole as a *-kind type variable (surface
            # holes are usually value-level; polymorphic holes need richer kinding).
            return ctrue, TypePolymorphism(name_a, Kind.STAR, TypeVar(name_a))
        case _:
            logger.log("SYNTH_TYPE", ("Unhandled:", t))
            logger.log("SYNTH_TYPE", ("Unhandled:", type(t)))
            assert False, f"Unhandled term {t} in synth. Type: {type(t)}"


def _try_check_recursor(ctx: TypingContext, t: Term, ty: Type) -> Constraint | None:
    """Path-sensitive checking of a fully-applied inductive eliminator.

    Surface ``match`` lowers to ``T_rec[..] scrut h_1 … h_n``. Elaboration fixes
    the eliminator's result *motive* to a bare base type, so the ordinary
    synth-then-subtype path checks every branch against an unrefined ``ret`` and
    proves the goal only on the (information-free) result -- dropping the matched
    constructor's refinement. Here we instead bind the motive to the *expected*
    type ``ty`` and check each handler against it. The dependent eliminator
    carries the constructor's refinement in as a proof witness (see
    ``expand_inductive_decls``), so each branch body is verified under that fact
    -- recovering match path-sensitivity.

    Returns the constraint, or ``None`` to fall back to the default rule when
    ``t`` is not a recognisable, fully-applied eliminator on a variable
    scrutinee.
    """
    # Only worth the extra work when the expected type carries a non-trivial
    # refinement: that is the obligation the matched constructor's fact helps
    # discharge. An unrefined motive is handled fine -- and far more cheaply --
    # by the default synth-then-subtype path, so skip the whole machinery (and
    # its per-branch re-checking) for the common case.
    ty_r = ensure_refined(ty)
    if not isinstance(ty_r, RefinedType) or (
        isinstance(ty_r.refinement, LiquidLiteralBool) and ty_r.refinement.value is True
    ):
        return None

    value_args: list[Term] = []
    cur: Term = t
    while isinstance(cur, Application):
        value_args.append(cur.arg)
        cur = cur.fun
    value_args.reverse()
    if not value_args:
        return None
    spine: list[tuple[str, object]] = []
    head: Term = cur
    while isinstance(head, (TypeApplication, RefinementApplication)):
        spine.append(("T", head.type) if isinstance(head, TypeApplication) else ("R", head.refinement))
        head = head.body
    spine.reverse()
    if not isinstance(head, Var) or not head.name.name.endswith("_rec"):
        return None
    from aeon.verification.constructor_registry import get_constructor_groups

    if head.name.name[: -len("_rec")] not in get_constructor_groups():
        return None
    rec_type = ctx.type_of(head.name)
    if rec_type is None:
        return None
    scrut = value_args[0]
    handlers = value_args[1:]
    scrut_inner = scrut.expr if isinstance(scrut, Annotation) else scrut
    if not isinstance(scrut_inner, Var):
        return None

    # The motive is the type-variable returned after peeling binders and arrows.
    peeled: Type = rec_type
    while isinstance(peeled, (TypePolymorphism, RefinementPolymorphism)):
        peeled = peeled.body
    res: Type = peeled
    while isinstance(res, AbstractionType):
        res = res.type
    if not isinstance(res, TypeVar):
        return None
    ret_var = res.name

    # Re-instantiate the eliminator with the spine's args, but bind the motive to
    # the expected type ``ty`` instead of its elaboration-erased base.
    inst: Type = rec_type
    for kind, val in spine:
        if isinstance(inst, TypePolymorphism) and kind == "T":
            assert isinstance(val, Type)
            repl = ty if inst.name == ret_var else fresh(ctx, val)
            inst = type_substitution(inst.body, inst.name, repl)
        elif isinstance(inst, RefinementPolymorphism) and kind == "R":
            if isinstance(val, ImplicitRefinementHole):
                inst = instantiate_refinement_with_horn_in_type(
                    inst.body, inst.name, inst.sort, Name("kappa", fresh_counter.fresh())
                )
            elif isinstance(val, Abstraction):
                inst = instantiate_refinement_in_type(inst.body, inst.name, val)
            else:
                return None
        else:
            return None
    if not isinstance(inst, AbstractionType):
        return None

    # ``inst`` is now ``(this: D) -> (case_1: CT_1) -> … -> ty``.
    rest: Type = substitution_in_type(inst.type, scrut_inner, inst.var_name)
    tyname = head.name.name[: -len("_rec")]
    constraints: list[Constraint] = [check(ctx, scrut, inst.var_type)]
    for h in handlers:
        if not isinstance(rest, AbstractionType):
            return None
        case_name, case_type, rest = rest.var_name, rest.var_type, rest.type
        constraints.append(_check_recursor_branch(ctx, h, case_type, tyname, case_name, scrut_inner))
    out: Constraint = constraints[0]
    for c in constraints[1:]:
        out = Conjunction(out, c)
    return out


def _check_recursor_branch(
    ctx: TypingContext,
    handler: Term,
    case_type: Type,
    tyname: str,
    case_name: Name,
    scrut: Var,
) -> Constraint:
    """Check one eliminator branch under the matched constructor's refinement.

    The branch handler ``λf₁ … f_k. body`` is checked against the case type
    ``(f₁) → … → (f_k) → motive`` (already carrying the expected motive); on top
    of the usual field hypotheses we add the constructor's *result* refinement,
    specialised to the scrutinee (``size this = size tl + 1`` becomes
    ``size scrut = size <field-for-tl> + 1``). That fact -- a pure measure
    statement, which is all aeon's SMT logic models about a datatype -- is what
    a non-dependent ``ret`` motive drops, and is exactly the match-branch
    hypothesis. Falls back to a plain check (motive only, no constructor fact)
    if the constructor's shape cannot be recovered."""
    plain = lambda: check(ctx, handler, case_type)  # noqa: E731
    ctor_full = f"{tyname}_{case_name.name[len('case_') :]}" if case_name.name.startswith("case_") else None
    ctor_type = next((tt for n, tt in ctx.vars() if n.name == ctor_full), None) if ctor_full else None
    if ctor_type is None:
        return plain()
    # Peel the constructor's binders/fields to reach its result refinement.
    cur: Type = ctor_type
    while isinstance(cur, (TypePolymorphism, RefinementPolymorphism)):
        cur = cur.body
    ctor_arg_names: list[Name] = []
    while isinstance(cur, AbstractionType):
        ctor_arg_names.append(cur.var_name)
        cur = cur.type
    res_ref = ensure_refined(cur)
    if not isinstance(res_ref, RefinedType):
        return plain()

    # Peel the handler's field binders against the case type, recording the
    # field types and the constructor-arg → handler-field name correspondence.
    fields: list[tuple[Name, Type]] = []
    ctor_to_field: dict[Name, LiquidTerm] = {}
    hh: Term = handler
    ct: Type = case_type
    while isinstance(ct, AbstractionType) and isinstance(hh, Abstraction):
        fn = hh.var_name
        fields.append((fn, ct.var_type))
        if len(fields) - 1 < len(ctor_arg_names):
            ctor_to_field[ctor_arg_names[len(fields) - 1]] = LiquidVar(fn)
        ct = substitution_in_type(ct.type, Var(fn), ct.var_name)
        hh = hh.body
    if isinstance(ct, AbstractionType):
        return plain()  # handler under-applied for this case — leave it to the default

    # fact = constructor result refinement, with the result binder set to the
    # scrutinee and constructor field names mapped to the handler's binders.
    fact: LiquidTerm = substitution_in_liquid(res_ref.refinement, LiquidVar(scrut.name), res_ref.name)
    for cn, fv in ctor_to_field.items():
        fact = substitution_in_liquid(fact, fv, cn)

    ctx2 = ctx
    for fn, ftype in fields:
        ctx2 = ctx2.with_var(fn, ftype)
    body_c = check(ctx2, hh, ct)
    c = implication_constraint(
        Name("_hyp", fresh_counter.fresh()),
        RefinedType(Name("_hypu", fresh_counter.fresh()), t_unit, fact),
        body_c,
    )
    for fn, ftype in reversed(fields):
        c = implication_constraint(fn, ftype, c)
    return c


def check(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
    try:
        assert wellformed(ctx, ty)
    except AssertionError:
        raise CoreWellformnessError(ty)
    match t, ty:
        case Abstraction(name, body), AbstractionType(var_name, var_type, ret):
            ret = substitution_in_type(ret, Var(name), var_name)
            c = check(ctx.with_var(name, var_type), body, ret)
            return implication_constraint(name, var_type, c, body.loc)
        case Let(name, val, body), _:
            (c1, t1) = synth(ctx, val)
            opened_binders: tuple[tuple[Name, Type], ...] = ()
            if isinstance(t1, ExistentialType):
                opened_binders = t1.binders
                t1 = t1.body
            nctx: TypingContext = ctx
            for bn, bt in opened_binders:
                nctx = nctx.with_var(bn, bt)
            nctx = nctx.with_var(name, t1)
            c2 = check(nctx, body, ty)
            reflected_impl = _reflected_impl_for(name, t1, val)
            inner = implication_constraint(name, t1, c2, body.loc, reflected_impl=reflected_impl)
            for bn, bt in reversed(opened_binders):
                inner = implication_constraint(bn, bt, inner, body.loc)
            return Conjunction(c1, inner)
        case Rec(var_name, var_type, var_value, body), _:
            if var_name in ctx.trusted_names:
                t1 = fresh(ctx, var_type)
                nrctx: TypingContext = ctx.with_var(var_name, t1)
                c2 = check(nrctx, body, ty)
                return implication_constraint(
                    var_name, t1, c2, body.loc, keep_refinements=True
                )
            has_metric = bool(t.decreasing_by)
            # See the ``synth`` Rec arm: a ``mutual`` group's inductive hypothesis
            # is only sound when every member carries a termination metric.
            group_has_metric = has_metric and all(bool(c.decreasing_by) for c in t.companions)
            t1 = fresh(ctx, var_type)
            # The recursive occurrence may assume the declared (refined) return
            # type as an inductive hypothesis only when a well-founded
            # termination metric justifies the induction. Without one, weaken
            # the hypothesis to the bare codomain so a non-terminating
            # definition cannot "prove" an absurd refinement (see
            # recursion_soundness_test.py). Non-recursive bindings are
            # unaffected: their body never references var_name.
            rec_t1 = t1 if group_has_metric else _erase_return_refinement(t1)
            rec_ctx: TypingContext = ctx.with_var(var_name, rec_t1)
            # Bring mutually-recursive siblings into scope for the value.
            comp_types: list[tuple[Name, Type]] = [(c.name, fresh(ctx, c.type)) for c in t.companions]
            for cname, ctype in comp_types:
                rec_ctx = rec_ctx.with_var(cname, ctype if group_has_metric else _erase_return_refinement(ctype))
            c1 = check(rec_ctx, var_value, var_type)
            nrctx: TypingContext = ctx.with_var(var_name, t1)
            # Termination obligations (incl. cross-function calls) need siblings.
            term_ctx: TypingContext = nrctx
            for cname, ctype in comp_types:
                term_ctx = term_ctx.with_var(cname, ctype)
            c2 = check(nrctx, body, ty)
            reflected_impl = _reflected_impl_for(
                var_name,
                t1,
                var_value,
                has_termination_metric=has_metric,
            )
            keep_refs = _is_trusted_native_value(var_value)
            c1 = implication_constraint(
                var_name, t1, c1, var_value.loc, reflected_impl=reflected_impl, keep_refinements=keep_refs
            )
            c2 = implication_constraint(
                var_name, t1, c2, body.loc, reflected_impl=reflected_impl, keep_refinements=keep_refs
            )
            term_c = termination_metric_constraints(t, term_ctx)
            term_c = implication_constraint(
                var_name, t1, term_c, var_value.loc, reflected_impl=reflected_impl, keep_refinements=keep_refs
            )
            # Declare mutually-recursive siblings so calls to them inside this
            # member's value translate (selfified applications such as
            # ``v == odd (n - 1)``). Reflect a sibling's definition when the group
            # is well-founded and its body reflects, so relational refinements
            # like ``{r | g r = x}`` can use it; otherwise declare it uninterpreted.
            for comp, (cname, ctype) in zip(t.companions, comp_types, strict=True):
                comp_reflected = (
                    _reflected_impl_for(cname, ctype, comp.value, has_termination_metric=group_has_metric)
                    if (group_has_metric and comp.value is not None)
                    else None
                )
                comp_keep = comp.value is not None and _is_trusted_native_value(comp.value)
                c1 = implication_constraint(
                    cname, ctype, c1, var_value.loc, reflected_impl=comp_reflected, keep_refinements=comp_keep
                )
            return Conjunction(Conjunction(c1, c2), term_c)
        case If(cond, then, otherwise), _:
            y = Name("_cond", fresh_counter.fresh())
            liq_cond = liquefy(cond)
            assert liq_cond is not None
            # Synth the condition so its refinement can be carried into
            # the branches: for ``cond : {b: Bool | r(b)}`` we add
            # ``r(liq_cond)`` to both branches' hypotheses, alongside
            # the truth/falsity fact. Existential binders are opened
            # into the branch context (mirroring how ``Let`` does it).
            (c_synth, t_cond) = synth(ctx, cond)
            ex_binders: tuple[tuple[Name, Type], ...] = ()
            if isinstance(t_cond, ExistentialType):
                ex_binders = t_cond.binders
                t_cond = t_cond.body
            c_sub = sub(ctx, t_cond, t_bool, cond.loc)
            c0 = Conjunction(c_synth, c_sub)
            branch_ctx = ctx
            for bn, bt in ex_binders:
                branch_ctx = branch_ctx.with_var(bn, bt)
            cond_ref: "LiquidTerm | None" = None
            t_cond_r = ensure_refined(t_cond)
            if isinstance(t_cond_r, RefinedType) and not (
                isinstance(t_cond_r.refinement, LiquidLiteralBool) and t_cond_r.refinement.value is True
            ):
                cond_ref = substitution_in_liquid(t_cond_r.refinement, liq_cond, t_cond_r.name)
            name_pos = Name("branch_pos", fresh_counter.fresh())
            c1 = implication_constraint(
                y,
                RefinedType(name_pos, t_int, _and(liq_cond, cond_ref)),
                check(branch_ctx, then, ty),
                then.loc,
            )
            name_neg = Name("branch_neg", fresh_counter.fresh())
            c2 = implication_constraint(
                y,
                RefinedType(
                    name_neg,
                    t_int,
                    _and(LiquidApp(Name("!", 0), [liq_cond]), cond_ref),
                ),
                check(branch_ctx, otherwise, ty),
                otherwise.loc,
            )
            if_constraint: Constraint = Conjunction(c0, Conjunction(c1, c2))
            for bn, bt in reversed(ex_binders):
                if_constraint = implication_constraint(bn, bt, if_constraint, t.loc)
            return if_constraint
        case TypeAbstraction(name, kind, body), TypePolymorphism(var_name, var_kind, var_body):
            if var_kind == Kind.BASE and kind != var_kind:
                raise CoreWrongKindInTypeApplicationError(
                    term=t,
                    type=ty,
                    actual_kind=var_kind,
                    expected_kind=var_kind,
                )
            itype = substitute_vartype(var_body, TypeVar(name), var_name)
            return check(ctx.with_typevar(name, var_kind), body, itype)

        case RefinementAbstraction(pname, psort, inner), RefinementPolymorphism(rname, rsort, rbody):
            c_sort = sub(ctx, psort, rsort, t.loc)
            # ``rsort`` is the full (possibly n-ary) predicate type.
            fk_type = _as_predicate_type(rsort)
            ctx_ext = ctx.with_var(pname, fk_type)
            body_open = substitution_liquid_in_type(rbody, LiquidVar(pname), rname)
            inner_sub = substitution_liquid_in_term(inner, LiquidVar(pname), rname)
            c_body = check(ctx_ext, inner_sub, body_open)
            return Conjunction(c_sort, UninterpretedFunctionDeclaration(pname, fk_type, c_body))

        # per tutorial fig 8.4 Chk-RAbs
        case _, RefinementPolymorphism(name, sort, body):
            # ρ = κ : sort; φ = λx.fκ(x). ``sort`` is the full (possibly n-ary)
            # predicate type ``d1 -> ... -> Bool``.
            fk_name = Name("_f" + name.name, fresh_counter.fresh())
            fk_type = _as_predicate_type(sort)
            # Γ' = Γ; fκ : sort
            ctx_ext = ctx.with_var(fk_name, fk_type)
            # s[ρ := fκ] — substitute κ → fk in the body type
            body_sub = substitution_liquid_in_type(body, LiquidVar(fk_name), name)
            # e[ρ := fκ] — substitute κ in types embedded in the term
            term_sub = substitution_liquid_in_term(t, LiquidVar(fk_name), name)
            c = check(ctx_ext, term_sub, body_sub)
            # Return (fκ :: sort → bool) ⇒ c
            return UninterpretedFunctionDeclaration(fk_name, fk_type, c)

        case _ if (rec_c := _try_check_recursor(ctx, t, ty)) is not None:
            # Fully-applied inductive eliminator (lowered ``match``): check each
            # branch against the expected motive so the matched constructor's
            # refinement reaches the branch body (path-sensitivity).
            return rec_c
        case _:
            (c, s) = synth(ctx, t)
            cp = sub(ctx, s, ty, t.loc)
            if cp == LiquidConstraint(LiquidLiteralBool(False)):
                raise CoreSubtypingError(ctx, t, s, ty)
            return Conjunction(c, cp)


def check_type(ctx: TypingContext, t: Term, ty: Type = top) -> bool:
    """Returns whether expression t has type ty in context ctx."""
    try:
        assert wellformed(ctx, ty)
        constraint = check(ctx, t, ty)
        v = entailment(ctx, constraint)
        return v
    except CoreTypeCheckingError:
        return False


def constraint_to_parts(
    c: Constraint, typing_ctx: TypingContext | None = None
) -> Iterable[tuple[Constraint, Location | None]]:
    """Prepares a constraint into a list of sub-problems for error messages.
    Yields (constraint, location) pairs where location is the AST location
    associated with the failing constraint part."""
    atoms = extract_qualifier_atoms(typing_ctx) if typing_ctx is not None else frozenset()
    for cons in conjunctive_normal_form(c):
        if not is_implication_true(cons):
            if not solve(cons, typing_ctx=typing_ctx, qualifier_atoms=atoms):
                vcs = split_or_in_conclusion(cons)
                for vc in vcs:
                    if not solve(vc, typing_ctx=typing_ctx, qualifier_atoms=atoms):
                        cons_simp = simplify_constraint(vc)
                        cons_clean, _ = remove_unrelated_context(cons_simp, ignore_vars=set())
                        loc = constraint_location(cons_clean)
                        yield cons_clean, loc
                        break


def check_type_errors(
    ctx: TypingContext,
    term: Term,
    expected_type: Type,
) -> Iterable[AeonError]:
    if not wellformed(ctx, expected_type):
        return [CoreWellformnessError(expected_type)]

    # Constraint-based type checking, then linearity checking. Both passes
    # are reported together so the user sees every diagnostic in one go.
    from aeon.typechecking.linearity import check_linearity

    try:
        constraint = check(ctx, term, expected_type)
        match entailment(ctx, constraint):
            case True:
                type_errors: list[AeonError] = []
            case False:
                full_constraint = entailment_context(ctx, constraint)
                type_errors = [
                    LiquidTypeCheckingFailedRelation(ctx, term, expected_type, vc, loc)
                    for vc, loc in constraint_to_parts(full_constraint, ctx)
                ]
    except CoreTypeCheckingError as e:
        return [e]

    linearity_errors = check_linearity(term, ctx)
    return type_errors + list(linearity_errors)
