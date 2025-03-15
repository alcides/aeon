from aeon.core.liquid import LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.types import AbstractionType, BaseType, Type, TypeVar
from aeon.typechecking.context import TypingContext
from aeon.typechecking.liquid import LiquidTypeCheckingContext, check_liquid, lower_abstraction_type, lower_context
from aeon.verification.smt import get_new_name, rename_constraint
from aeon.verification.vcs import (
    Constraint,
    Implication,
    LiquidConstraint,
    Top,
    Conjunction,
    TypeVarDeclaration,
    UninterpretedFunctionDeclaration,
)


def wellformed_constraint_liquid(ctx: LiquidTypeCheckingContext, c: Constraint) -> None:
    match c:
        case LiquidConstraint(expr):
            assert check_liquid(ctx, expr, BaseType("Bool")), f"Expected boolean expression, got {expr}."
        case Conjunction(c1, c2):
            wellformed_constraint_liquid(ctx, c1)
            wellformed_constraint_liquid(ctx, c2)
        case UninterpretedFunctionDeclaration(name, ft, seq):
            nctx = LiquidTypeCheckingContext(
                ctx.known_types, ctx.variables, ctx.functions | {name: lower_abstraction_type(ft)}
            )
            assert isinstance(ft, AbstractionType), f"{ft} is expected to be an AbstractionType."
            wellformed_constraint_liquid(nctx, seq)
        case TypeVarDeclaration(name, seq):
            nctx = LiquidTypeCheckingContext(ctx.known_types + [BaseType(name)], ctx.variables, ctx.functions)
            assert name in ctx.known_types, f"Type {name} not found in known types ({ctx.known_types})."
            wellformed_constraint_liquid(nctx, seq)
        case Implication(name, base, pred, seq):
            if isinstance(base, Top):
                assert False, "Top type is not allowed in Implication."
            nctx = LiquidTypeCheckingContext(ctx.known_types, ctx.variables | {name: base}, ctx.functions)
            assert isinstance(base, BaseType), f"Expected BaseType, got {base}."
            assert name not in ctx.variables, f"Variable {name} already exists in context."

            assert check_liquid(nctx, pred, BaseType("Bool")), (
                f"Predicate {pred} is either not valid, or not of type boolean."
            )
            wellformed_constraint_liquid(nctx, seq)
        case _:
            assert False, f"Wellformeness of constraint {c} ({type(c)}) not defined"


def canonicalize_type(t: Type) -> Type:
    match t:
        case Top():
            return BaseType("Unit")
        case BaseType(_):
            return t
        case TypeVar(tv):
            return BaseType(tv)
        case AbstractionType(name, at, rt):
            return AbstractionType(name, canonicalize_type(at), canonicalize_type(rt))
        case _:
            assert False, f"No canonicalization for type {t} ({type(t)})"


def canonicalize_constraint(c: Constraint, stack: list[str] = None) -> Constraint:
    if stack is None:
        stack = []

    match c:
        case LiquidConstraint(expr):
            return LiquidConstraint(expr)
        case Conjunction(c1, c2):
            return Conjunction(canonicalize_constraint(c1, stack), canonicalize_constraint(c2, stack))
        case UninterpretedFunctionDeclaration(name, ft, seq):
            new_name = get_new_name(name, stack)
            if new_name != name:
                nseq = rename_constraint(c, name, new_name)
            else:
                nseq = seq
            nseq = canonicalize_constraint(nseq, stack + [new_name])
            nty = canonicalize_type(ft)
            assert isinstance(nty, AbstractionType), f"Expected AbstractionType, got {nty}."
            return UninterpretedFunctionDeclaration(new_name, nty, nseq)
        case TypeVarDeclaration(name, seq):
            if name in stack:
                assert False, f"Type variable {name} is already in the stack."
            return TypeVarDeclaration(name, canonicalize_constraint(seq, stack + [name]))
        case Implication(name, base, pred, seq):
            new_name = get_new_name(name, stack)
            if new_name != name:
                npred = substitution_in_liquid(pred, LiquidVar(new_name), name)
                nseq = rename_constraint(c, name, new_name)
            else:
                npred = pred
                nseq = seq
            nseq = canonicalize_constraint(nseq, stack + [new_name])
            nty = canonicalize_type(base)
            assert isinstance(nty, BaseType) or isinstance(nty, Top) or isinstance(nty, TypeVar), (
                f"Expected BaseType, got {nty}."
            )

            return Implication(new_name, nty, npred, nseq)
        case _:
            assert False, f"Canonicalization of constraint {c} ({type(c)}) not defined"


def wellformed_constraint(ctx: TypingContext, c: Constraint) -> bool:
    lctx = lower_context(ctx)
    wellformed_constraint_liquid(lctx, c)
    return True
