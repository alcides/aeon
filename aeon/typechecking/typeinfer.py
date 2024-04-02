from __future__ import annotations
from typing import Tuple

from loguru import logger

from aeon.core.instantiation import type_substitution
from aeon.core.liquid import LiquidApp, LiquidHole, LiquidTerm
from aeon.core.liquid import LiquidLiteralBool
from aeon.core.liquid import LiquidLiteralFloat
from aeon.core.liquid import LiquidLiteralInt
from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import ops
from aeon.core.substitutions import liquefy
from aeon.core.substitutions import substitute_vartype
from aeon.core.substitutions import substitution_in_type
from aeon.core.terms import Abstraction
from aeon.core.terms import Annotation
from aeon.core.terms import Application
from aeon.core.terms import Hole
from aeon.core.terms import If
from aeon.core.terms import Let
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import TypeAbstraction
from aeon.core.terms import TypeApplication
from aeon.core.terms import Var
from aeon.core.types import AbstractionType, Bottom, ExistentialType, Top
from aeon.core.types import BaseKind
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import Type
from aeon.core.types import TypePolymorphism
from aeon.core.types import TypeVar
from aeon.core.types import args_size_of_type
from aeon.core.types import bottom
from aeon.core.types import extract_parts
from aeon.core.types import t_bool
from aeon.core.types import t_float
from aeon.core.types import t_int
from aeon.core.types import t_unit
from aeon.core.types import type_free_term_vars
from aeon.prelude.prelude import (
    INTEGER_ARITHMETIC_OPERATORS,
    FLOAT_ARITHMETIC_OPERATORS,
    COMPARISON_OPERATORS,
    LOGICAL_OPERATORS,
    EQUALITY_OPERATORS,
)
from aeon.typechecking.context import TypingContext
from aeon.typechecking.entailment import entailment
from aeon.verification.helpers import simplify_constraint
from aeon.verification.horn import fresh
from aeon.verification.sub import implication_constraint
from aeon.verification.sub import sub
from aeon.verification.vcs import Conjunction
from aeon.verification.vcs import Constraint
from aeon.verification.vcs import LiquidConstraint

ctrue = LiquidConstraint(LiquidLiteralBool(True))


class CouldNotGenerateConstraintException(Exception):
    pass


class FailedConstraintException(Exception):

    def __init__(self, ctx, t, ty, ks):
        self.ctx = ctx
        self.t = t
        self.ty = ty
        self.ks = ks

    def __str__(self):
        return f"Constraint violated when checking if {self.t} : {self.ty}: \n {self.ks}"


def eq_ref(var_name: str, type_name: str) -> LiquidTerm:
    return LiquidApp(
        "==",
        [
            LiquidVar(var_name),
            LiquidVar(type_name),
        ],
    )


def and_ref(cond1: LiquidTerm, cond2: LiquidTerm) -> LiquidTerm:
    return LiquidApp("&&", [cond1, cond2])


def refine_type(ctx: TypingContext, ty: Type, vname: str):
    """The refine function is the selfication with support for existentials"""
    match ty:
        case BaseType(name=_) | Top() | Bottom():
            name = ctx.fresh_var()
            return RefinedType(name, ty, eq_ref(name, vname))
        case RefinedType(name=name, type=ty, refinement=cond):
            name = ctx.fresh_var()
            assert name != vname
            return RefinedType(name, ty, and_ref(cond, eq_ref(name, vname)))
        case ExistentialType(var_name=var_name, var_type=var_type, type=ity):
            return ExistentialType(var_name, var_type, refine_type(ctx, ity, vname))
        case AbstractionType(var_name=var_name, var_type=var_type, type=type):
            return ty
        case _:
            assert False


def argument_is_typevar(ty: Type):
    return (
        isinstance(ty, TypeVar)
        or isinstance(
            ty,
            RefinedType,
        )
        and isinstance(ty.type, TypeVar)
    )


def extract_abstraction_type(ty: Type) -> Tuple[AbstractionType, list[Tuple[str, Type]]]:
    binders = []
    while isinstance(ty, ExistentialType):
        binders.append((ty.var_name, ty.var_type))
        ty = ty.type
    assert isinstance(ty, AbstractionType)
    return ty, binders


def prim_litbool(t: bool) -> RefinedType:
    if t:
        return RefinedType("v", t_bool, LiquidVar("v"))
    else:
        return RefinedType("v", t_bool, LiquidApp("!", [LiquidVar("v")]))


def prim_litint(t: int) -> RefinedType:
    return RefinedType(
        "v",
        t_int,
        LiquidApp("==", [LiquidVar("v"), LiquidLiteralInt(t)]),
    )


def prim_litfloat(t: float) -> RefinedType:
    return RefinedType(
        "v",
        t_float,
        LiquidApp("==", [LiquidVar("v"), LiquidLiteralFloat(t)]),
    )


def prim_op(t: str) -> Type:
    i1: Type
    i2: Type
    o: Type

    if t in INTEGER_ARITHMETIC_OPERATORS:
        i1 = i2 = t_int
        o = t_int
    elif t in FLOAT_ARITHMETIC_OPERATORS:
        i1 = i2 = t_float
        o = t_float
    elif t in COMPARISON_OPERATORS:
        i1 = i2 = t_int
        o = t_bool
    elif t in LOGICAL_OPERATORS:
        i1 = i2 = o = t_bool
    elif t in EQUALITY_OPERATORS:
        i1 = TypeVar("_op_1")
        i2 = TypeVar("_op_1")
        o = t_bool
    else:
        print(">>", t)
        assert False

    return AbstractionType(
        "x",
        i1,
        AbstractionType(
            "y",
            i2,
            RefinedType(
                "z",
                o,
                LiquidApp(
                    "==",
                    [
                        LiquidVar("z"),
                        LiquidApp(
                            t,
                            [LiquidVar("x"), LiquidVar("y")],
                        ),
                    ],
                ),
            ),
        ),
    )


def rename_liquid_term(refinement, old_name, new_name):
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
    elif isinstance(refinement, LiquidHole):
        if refinement.name == old_name:
            return LiquidHole(
                new_name,
                [(rename_liquid_term(x, old_name, new_name), t) for (x, t) in refinement.argtypes],
            )
        else:
            return LiquidHole(
                refinement.name,
                [(rename_liquid_term(x, old_name, new_name), t) for (x, t) in refinement.argtypes],
            )
    else:
        assert False


def renamed_refined_type(ty: RefinedType) -> RefinedType:
    old_name = ty.name
    new_name = "_inner_" + old_name

    refinement = rename_liquid_term(ty.refinement, old_name, new_name)
    return RefinedType(new_name, ty.type, refinement)


# patterm matching term
def synth(ctx: TypingContext, t: Term) -> tuple[Constraint, Type]:
    if isinstance(t, Literal) and t.type == t_unit:
        return (
            ctrue,
            prim_litbool(True),
        )  # TODO: Unit is encoded as True, replace with custom Sort
    elif isinstance(t, Literal) and t.type == t_bool:
        assert isinstance(t.value, bool)
        return (ctrue, prim_litbool(t.value))
    elif isinstance(t, Literal) and t.type == t_int:
        assert isinstance(t.value, int)
        return (ctrue, prim_litint(t.value))
    elif isinstance(t, Literal) and t.type == t_float:
        assert isinstance(t.value, float)
        return (ctrue, prim_litfloat(t.value))
    elif isinstance(t, Literal):
        return (ctrue, t.type)
    elif isinstance(t, Var):
        if t.name in ops:
            return (ctrue, prim_op(t.name))
        ty = ctx.type_of(t.name)
        if ty is not None:
            return (ctrue, refine_type(ctx, ty, t.name))
        raise CouldNotGenerateConstraintException(
            f"Variable {t.name} not in context",
        )
    elif isinstance(t, Application):
        (c1, ty1) = synth(ctx, t.fun)
        (c2, ty2) = synth(ctx, t.arg)

        abstraction_type, binders = extract_abstraction_type(ty1)

        if isinstance(abstraction_type, AbstractionType):
            argument_type = abstraction_type.var_type
            return_type = abstraction_type.type

            if argument_is_typevar(argument_type):
                (_, b, _) = extract_parts(argument_type)
                assert isinstance(b, TypeVar)
                argument_type = substitute_vartype(argument_type, ty2, b.name)
                return_type = substitute_vartype(return_type, ty2, b.name)
                c3 = ctrue
            else:
                c3 = sub(ty2, argument_type)
            new_name = ctx.fresh_var()
            return_type = type_substitution(return_type, abstraction_type.var_name, new_name)
            nt = ExistentialType(var_name=new_name, var_type=argument_type, type=return_type)
            for aname, aty in binders[::-1]:
                nt = ExistentialType(aname, aty, nt)
            return Conjunction(Conjunction(c1, c2), c3), nt

            # This is the solution to handle polymorphic "==" in refinements.
            # if argument_is_typevar(ty.var_type):
            #     (_, b, _) = extract_parts(ty.var_type)
            #     assert isinstance(b, TypeVar)
            #     (cp, at) = synth(ctx, t.arg)
            #     if isinstance(at, RefinedType):
            #         at = at.type  # This is a hack before inference
            #     return_type = substitute_vartype(ty.type, at, b.name)
            # else:
            #     cp = check(ctx, t.arg, ty.var_type)
            #     return_type = ty.type
            # t_subs = substitution_in_type(return_type, t.arg, ty.var_name)
            # c0 = Conjunction(c, cp)
            # # vs: list[str] = list(variables_free_in(c0))
            # return (c0, t_subs)
        else:
            raise CouldNotGenerateConstraintException(
                f"Application {t} is not a function.",
            )
    elif isinstance(t, Let):
        (c1, t1) = synth(ctx, t.var_value)
        nctx: TypingContext = ctx.with_var(t.var_name, t1)
        (c2, t2) = synth(nctx, t.body)
        term_vars = type_free_term_vars(t1)
        assert t.var_name not in term_vars
        r = (Conjunction(c1, implication_constraint(t.var_name, t1, c2)), t2)
        return r
    elif isinstance(t, Rec):
        nrctx: TypingContext = ctx.with_var(t.var_name, t.var_type)
        c1 = check(nrctx, t.var_value, t.var_type)
        (c2, t2) = synth(nrctx, t.body)

        c1 = implication_constraint(t.var_name, t.var_type, c1)
        c2 = implication_constraint(t.var_name, t.var_type, c2)
        return Conjunction(c1, c2), t2
    elif isinstance(t, Annotation):
        ty = fresh(ctx, t.type)
        c = check(ctx, t.expr, ty)
        return c, ty
    elif isinstance(t, TypeApplication):
        (c, tabs) = synth(ctx, t.body)
        assert isinstance(tabs, TypePolymorphism)  # TODO: Check this
        ty = fresh(ctx, t.type)
        s = type_substitution(tabs.body, tabs.name, ty)
        return c, s
    elif isinstance(t, Hole):
        return ctrue, bottom
    # TODO: add if term
    # elif isinstance(t, If):
    #     y = ctx.fresh_var()
    #     (c0, t0) = synth(ctx, t.cond)
    #     if not check_type(ctx, t.cond, t_bool):
    #         raise CouldNotGenerateConstraintException("If condition not boolean")
    #
    #     (c1, t1) = synth(ctx, t.then)
    #     (c2, t2) = synth(ctx, t.otherwise)
    #     t1 = ensure_refined(t1)
    #     t2 = ensure_refined(t2)
    #     assert t1.type == t2.type
    #     # t1s = substitution_in_liquid(t1.refinement, LiquidVar(y), t1.name)
    #     # t2s = substitution_in_liquid(t2.refinement, LiquidVar(y), t2.name)
    #     # print(t1s)
    #     # print(t2s)
    #     liquid_term_if = liquefy_if(t)
    #     print("term----", t)
    #     print("liquidterm----", liquid_term_if)
    #     x = Conjunction(c0, Conjunction(c1, c2)), RefinedType(y, t1.type, liquid_term_if)
    #     print(x)
    #     # return Conjunction(c0, Conjunction(c1, c2)), RefinedType(y, t1.type, LiquidApp("||", [t1s, t2s]))
    #     return x
    else:
        logger.log("SYNTH_TYPE", ("Unhandled:", t))
        logger.log("SYNTH_TYPE", ("Unhandled:", type(t)))
        assert False


def wrap_checks(f):
    """Decorate that performs intermediate checks to the SMT solver."""

    def check_(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
        k = f(ctx, t, ty)
        ks = simplify_constraint(k)
        if ks == LiquidConstraint(LiquidLiteralBool(False)):
            raise FailedConstraintException(ctx, t, ty, ks)
        else:
            return k

    return check_


# patterm matching term
# @wrap_checks  # DEMO1
def check(ctx: TypingContext, t: Term, ty: Type) -> Constraint:
    if isinstance(t, Abstraction) and isinstance(
        ty,
        AbstractionType,
    ):  # ??? (\__equal_1__ -> (let _anf_1 = (== _anf_1) in(_anf_1 __equal_1__))) , basetype INT
        ret = substitution_in_type(ty.type, Var(t.var_name), ty.var_name)
        c = check(ctx.with_var(t.var_name, ty.var_type), t.body, ret)
        return implication_constraint(t.var_name, ty.var_type, c)

    elif isinstance(t, Let):
        (c1, t1) = synth(ctx, t.var_value)
        nctx: TypingContext = ctx.with_var(t.var_name, t1)
        c2 = check(nctx, t.body, ty)
        return Conjunction(c1, implication_constraint(t.var_name, t1, c2))

    elif isinstance(t, Rec):
        t1 = fresh(ctx, t.var_type)
        nrctx: TypingContext = ctx.with_var(t.var_name, t1)
        c1 = check(nrctx, t.var_value, t.var_type)
        c2 = check(nrctx, t.body, ty)
        c1 = implication_constraint(t.var_name, t1, c1)
        c2 = implication_constraint(t.var_name, t1, c2)
        return Conjunction(c1, c2)
    elif isinstance(t, If):
        y = ctx.fresh_var()
        liq_cond = liquefy(t.cond)
        assert liq_cond is not None
        if not check_type(ctx, t.cond, t_bool):
            raise CouldNotGenerateConstraintException(
                "If condition not boolean",
            )
        c0 = check(ctx, t.cond, t_bool)
        c1 = implication_constraint(
            y,
            RefinedType("branch_", t_int, liq_cond),
            check(ctx, t.then, ty),
        )
        c2 = implication_constraint(
            y,
            RefinedType("branch_", t_int, LiquidApp("!", [liq_cond])),
            check(ctx, t.otherwise, ty),
        )
        return Conjunction(c0, Conjunction(c1, c2))
    elif isinstance(t, TypeAbstraction) and isinstance(ty, TypePolymorphism):
        ty_right = type_substitution(ty, ty.name, TypeVar(t.name))
        assert isinstance(ty_right, TypePolymorphism)
        if ty_right.kind == BaseKind() and t.kind != ty_right.kind:
            return LiquidConstraint(LiquidLiteralBool(False))
        return check(ctx.with_typevar(t.name, t.kind), t.body, ty_right.body)
    else:
        (c, s) = synth(ctx, t)
        cp = sub(s, ty)
        return Conjunction(c, cp)




def check_type(ctx: TypingContext, t: Term, ty: Type) -> bool:
    """Returns whether expression t has type ty in context ctx."""
    try:
        constraint = check(ctx, t, ty)
        return entailment(ctx, constraint)
    except CouldNotGenerateConstraintException as e:
        logger.info(f"Could not generate constraint: f{e}")
        return False
    except FailedConstraintException as e:
        logger.info(f"Could not prove constraint: f{e}")
        return False


class CouldNotProveTypingRelation(Exception):
    def __init__(self, context: TypingContext, term: Term, type: Type):
        self.context = context
        self.term = term
        self.type = type

    def __str__(self):
        return f"Could not prove typing relation (Context: {self.context}) (Term: {self.term}) (Type: {self.type})."


def check_type_errors(
    ctx: TypingContext,
    t: Term,
    ty: Type,
) -> list[Exception]:
    """Checks whether t as type ty in ctx, but returns a list of errors."""
    try:
        constraint = check(ctx, t, ty)
        print(f"Constraint: {constraint}")
        r = entailment(ctx, constraint)
        if r:
            return []
        else:
            return [CouldNotProveTypingRelation(ctx, t, ty)]
    except CouldNotGenerateConstraintException as e:
        return [e]
    except FailedConstraintException as e:
        return [e]


def is_subtype(ctx: TypingContext, subt: Type, supt: Type):
    assert not isinstance(supt, ExistentialType)
    if args_size_of_type(subt) != args_size_of_type(supt):
        return False
    if subt == supt:
        return True
    if isinstance(subt, RefinedType) and subt.type == supt:
        return True
    c = sub(subt, supt)
    if isinstance(c, LiquidLiteralBool):
        return c.value
    return entailment(ctx, c)


# TODO: Move this method elsewhere?
def check_and_log_type_errors(ctx: TypingContext, p: Term, top: Type):
    """This method is designed to be called from the CLI, so it contains prints
    instead of a logger."""
    errors = check_type_errors(ctx, p, top)
    if errors:
        for error in errors:
            print(error)
        return True
    return False
