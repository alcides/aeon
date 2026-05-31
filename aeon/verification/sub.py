from __future__ import annotations

from loguru import logger

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidTerm
from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, RefinementPolymorphism, TypeConstructor, TypeVar
from aeon.core.types import ExistentialType
from aeon.core.types import RefinedType
from aeon.core.types import Top
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import t_unit
from aeon.typechecking.context import TypingContext
from aeon.utils.location import Location
from aeon.verification.vcs import Conjunction, UninterpretedFunctionDeclaration
from aeon.verification.vcs import ReflectedFunctionDeclaration
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import Implication
from aeon.verification.vcs import LiquidConstraint
from aeon.utils.name import Name, fresh_counter

ctrue = LiquidConstraint(LiquidLiteralBool(True))
cfalse = LiquidConstraint(LiquidLiteralBool(False))


def ensure_refined(t: Type) -> Type:
    """Ensures that the Base Types and TypeVars are refined. All other types remain the same."""
    match t:
        case RefinedType(_, _, _):
            return t
        case TypeVar(Name(name)):
            return RefinedType(Name(f"singleton_{name}", fresh_counter.fresh()), t, LiquidLiteralBool(True))
        case TypeConstructor(Name(name), _):
            return RefinedType(Name(f"singleton_{name}", fresh_counter.fresh()), t, LiquidLiteralBool(True))
        case _:
            return t


def is_first_order_function(at: AbstractionType):
    v: Type = at
    while isinstance(v, TypePolymorphism) or isinstance(v, RefinementPolymorphism):
        if isinstance(v, TypePolymorphism):
            v = v.body
        else:
            v = v.body
    while isinstance(v, AbstractionType):
        match v.var_type:
            case AbstractionType(_, _, _):
                return False
            case (
                Top()
                | RefinedType(_, _, _)
                | TypeVar(_)
                | TypeConstructor(_, _)
                | TypePolymorphism(_, _, _)
                | RefinementPolymorphism(_, _, _)
            ):
                pass
            case _:
                assert False
        v = v.type
    return True


def lower_constraint_type(ttype: Type) -> Type:
    match ttype:
        case TypeVar(name):
            return TypeConstructor(name)
        case Top():
            return t_unit
        case AbstractionType(name, b, r):
            return AbstractionType(name, lower_constraint_type(b), lower_constraint_type(r))
        case TypePolymorphism(_, _, body):
            return lower_constraint_type(body)
        case RefinementPolymorphism(_, _, body):
            return lower_constraint_type(body)
        case RefinedType(_, t, _):
            return lower_constraint_type(t)
        case TypeConstructor(name, args):
            # Preserve the args (lowering each in turn). The SMT layer
            # mangles parametric type constructors into per-instantiation
            # sort names via ``_mangled_tc_name`` so each ``Pair Int Int``,
            # ``Pair Dataset Dataset`` etc. becomes a distinct sort, and
            # ``_specialize_liquid_term`` can monomorphise polymorphic
            # functions over them at each call site.
            return TypeConstructor(name, [lower_constraint_type(a) for a in args])

        case _:
            assert False, f"Unsupport type in constraint {ttype} ({type(ttype)})"


def _has_concrete_base_result(ty: Type) -> bool:
    """True when peeling all ``forall`` binders and value arrows lands on a
    concrete base type (a ``TypeConstructor``, possibly refined). Polymorphic
    functions whose result is a bare type variable — notably the ``native`` and
    ``uninterpreted`` builtins, typed ``forall a, … -> {x:a | false}`` — have no
    SMT sort and must not be declared as uninterpreted functions."""
    v: Type = ty
    while isinstance(v, (TypePolymorphism, RefinementPolymorphism)):
        v = v.body
    while isinstance(v, AbstractionType):
        v = v.type
    if isinstance(v, RefinedType):
        v = v.type
    return isinstance(v, TypeConstructor)


def implication_constraint(
    name: Name,
    ty: Type,
    c: Constraint,
    loc: Location | None = None,
    reflected_impl: tuple[tuple[Name, ...], LiquidTerm] | None = None,
) -> Constraint:
    match ty:
        case Top() | TypeVar(_) | TypeConstructor(_, _):
            basety = lower_constraint_type(ty)
            assert isinstance(basety, TypeConstructor)
            return Implication(name, basety, LiquidLiteralBool(True), c, loc=loc)
        case RefinedType(tname, ttype, tref):
            ref_subs = substitution_in_liquid(tref, LiquidVar(name), tname)
            ltype = lower_constraint_type(ttype)
            assert isinstance(ltype, TypeConstructor) or isinstance(ltype, TypeVar)
            return Implication(name, ltype, ref_subs, c, loc=loc)
        case AbstractionType(_, _, _):
            if is_first_order_function(ty):
                absty = lower_constraint_type(ty)
                assert isinstance(absty, AbstractionType)
                if reflected_impl is not None:
                    (params, body) = reflected_impl
                    return ReflectedFunctionDeclaration(name, absty, params, body, c)
                return UninterpretedFunctionDeclaration(name, absty, c)
            else:
                return c
        case TypePolymorphism(_, _, _) | RefinementPolymorphism(_, _, _):
            lowered = lower_constraint_type(ty)
            if not isinstance(lowered, AbstractionType):
                # Higher-order or otherwise non-first-order polymorphic
                # types stay opaque — no constraint contribution.
                return c
            if reflected_impl is not None:
                (params, body) = reflected_impl
                return ReflectedFunctionDeclaration(name, lowered, params, body, c)
            # Declare first-order polymorphic functions (e.g. typeclass method
            # projections) as uninterpreted so their applications can appear in
            # refinements. Type variables remain as ``TypeVar`` in arg positions;
            # ``_specialize_liquid_term`` monomorphises per call. Skip functions
            # whose result is a bare type variable (native/uninterpreted
            # builtins) — they have no SMT sort.
            if is_first_order_function(lowered) and _has_concrete_base_result(ty):
                return UninterpretedFunctionDeclaration(name, lowered, c)
            return c
        case _:
            assert False


def base_subtype_constraint(
    ctx: TypingContext,
    ty1: Type,
    ty2: Type,
    loc: Location | None = None,
) -> Constraint | None:
    """Subtyping between the *unrefined cores* of two types (``TypeConstructor``
    or ``TypeVar``), accounting for the variance of constructor arguments.

    Returns the constraint witnessing ``ty1 <: ty2`` ignoring any surrounding
    refinement, or ``None`` when the heads are incompatible (different
    constructor name, arity, or type variable).

    Type constructors in aeon are immutable inductive datatypes (``List``,
    ``Maybe``, ``Pair``, ``Tree`` …), so their arguments are **covariant**:
    ``C a`` <: ``C b`` whenever ``a`` <: ``b``. This mirrors Liquid Haskell,
    where element refinements flow covariantly through containers
    (``List {v:Int | v > 0}`` is a subtype of ``List Int``).

    Covariance is sound here because every parameter of an inductive type occurs
    only in positive (constructor-result / field) positions. A parameter used in
    a negative position (e.g. a function-typed field ``k : a -> Int``) would be
    contravariant/invariant and needs declared-or-inferred per-parameter
    variance — see issue #298.
    """
    match ty1, ty2:
        case TypeConstructor(name1, args1), TypeConstructor(name2, args2):
            if name1 != name2 or len(args1) != len(args2):
                return None
            c: Constraint = ctrue
            for a1, a2 in zip(args1, args2):
                c = Conjunction(c, sub(ctx, a1, a2, loc))
            return c
        case _:
            return ctrue if ty1 == ty2 else None


def sub(ctx: TypingContext, t1: Type, t2: Type, loc: Location | None = None) -> Constraint:
    if t2 == Top():
        return ctrue
    # Form B existential subtype: skolemise each binder by introducing it as
    # an implication assumption, then recurse on the body. Binders to the
    # right may mention earlier binders, so we wrap from innermost out.
    if isinstance(t1, ExistentialType):
        c = sub(ctx, t1.body, t2, loc)
        for bn, bt in reversed(t1.binders):
            c = implication_constraint(bn, bt, c, loc)
        return c
    # Existential on the supertype side would mean "there exists a witness …".
    # Skolemising naively is unsound; we don't currently produce existentials
    # in supertype position, so treat it as opaque for now.
    if isinstance(t2, ExistentialType):
        return sub(ctx, t1, t2.body, loc)
    match (ensure_refined(t1), ensure_refined(t2)):
        case RefinedType(n1, ty1, r1), RefinedType(n2, ty2, r2):
            if ty2 == Top():
                return ctrue
            # Subtype the unrefined cores first. This is where constructor-arg
            # variance lives: ``ensure_refined`` wraps every bare
            # ``TypeConstructor``/``TypeVar`` into a ``RefinedType``, so two
            # ``List …`` always reach this arm rather than the TypeConstructor
            # arm below — comparing args with ``!=`` here used to force
            # invariance. ``base_subtype_constraint`` instead recurses
            # covariantly into the arguments (see issue #298).
            args_c = base_subtype_constraint(ctx, ty1, ty2, loc)
            if args_c is None:
                return cfalse

            new_name: Name = Name(n1.name + n2.name, fresh_counter.fresh())

            # Performs substition on t2 to have the same name of t1
            r2_ = substitution_in_liquid(r2, LiquidVar(new_name), n2)
            r1_ = substitution_in_liquid(r1, LiquidVar(new_name), n1)
            lowert = lower_constraint_type(ty1)
            assert isinstance(lowert, TypeConstructor)
            rconstraint = Implication(new_name, lowert, r1_, LiquidConstraint(r2_, loc=loc), loc=loc)

            return Conjunction(args_c, rconstraint) if args_c is not ctrue else rconstraint
        case TypePolymorphism(_, _, _), _:
            return ctrue
        case RefinementPolymorphism(_, _, _), _:
            return ctrue
        case AbstractionType(a1, t1, rt1), AbstractionType(a2, t2, rt2):
            new_name_a: Name = Name(a1.name + a2.name, fresh_counter.fresh())

            c0 = sub(ctx, t2, t1, loc)
            rt1_ = substitution_in_type(rt1, Var(new_name_a), a1)
            rt2_ = substitution_in_type(rt2, Var(new_name_a), a2)
            c1 = sub(ctx, rt1_, rt2_, loc)
            return Conjunction(c0, implication_constraint(new_name_a, t2, c1, loc))
        case TypeConstructor(_, _) as tc1, TypeConstructor(_, _) as tc2:
            # Defensive: ``ensure_refined`` normally wraps bare type
            # constructors into ``RefinedType`` (handled above), so this arm is
            # only reached if a non-refined constructor ever flows in. Use the
            # same covariant rule as the refined path.
            args_c = base_subtype_constraint(ctx, tc1, tc2, loc)
            return cfalse if args_c is None else args_c
        case _:
            logger.error(f"Failed subtyping by exhaustion: {t1} <: {t2}")
            return cfalse
