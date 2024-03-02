from __future__ import annotations

from aeon.core.terms import Abstraction
from aeon.core.terms import Application
from aeon.core.terms import If
from aeon.core.terms import Literal
from aeon.core.terms import Rec
from aeon.core.terms import Term
from aeon.core.terms import Var
from aeon.core.types import AbstractionType
from aeon.core.types import args_size_of_type
from aeon.core.types import base
from aeon.core.types import BaseType
from aeon.core.types import RefinedType
from aeon.core.types import t_bool
from aeon.core.types import t_int
from aeon.core.types import Type
from aeon.synthesis.choice_manager import ChoiceManager
from aeon.synthesis.exceptions import NoMoreBudget
from aeon.synthesis.smt_synthesis import smt_synth_int_lit
from aeon.synthesis.sources import RandomSource
from aeon.synthesis.type_synthesis import synth_type
from aeon.typechecking.context import EmptyContext
from aeon.typechecking.context import TypeBinder
from aeon.typechecking.context import TypingContext
from aeon.typechecking.context import VariableBinder
from aeon.typechecking.typeinfer import check_type
from aeon.typechecking.typeinfer import is_subtype

DEFAULT_DEPTH = 9


def synth_literal(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = DEFAULT_DEPTH,
) -> Literal | None:
    if isinstance(ty, BaseType):
        if ty == t_int:
            return Literal(r.next_integer(), ty)
        elif ty == t_bool:
            return Literal(r.choose([True, False]), ty)
        else:
            assert False
    elif isinstance(ty, RefinedType):
        if ty.type == t_int:
            v = smt_synth_int_lit(ctx, ty, r.next_integer())
            if v is not None:
                return Literal(v, t_int)
        while man.budget > 0:
            man.checkpoint()
            k = synth_literal(man, r, ctx, ty.type)
            if k and check_type(ctx, k, ty):
                return k
            else:
                print("(d) does not typecheck", k, type(k), ty)
                man.undo_choice()
        raise NoMoreBudget()
    else:
        raise NoMoreBudget()


def vars_of_type(
    ctx: TypingContext,
    ty: Type,
    ictx: TypingContext | None = None,
) -> list[str]:
    if ictx is None:
        return vars_of_type(ctx, ty, ctx)
    if isinstance(ictx, EmptyContext):
        return []
    elif isinstance(ictx, VariableBinder):
        rest = vars_of_type(ctx, ty, ictx.prev)
        if is_subtype(ctx, ictx.type, ty):
            return [ictx.name] + rest
        else:
            return rest
    elif isinstance(ictx, TypeBinder):
        return vars_of_type(ctx, ty, ictx.prev)
    else:
        print(ictx, type(ictx))
        assert False


def synth_var(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = DEFAULT_DEPTH,
):
    candidates = vars_of_type(ctx, ty)
    if candidates:
        return Var(r.choose(candidates))
    raise NoMoreBudget()


def synth_app(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = DEFAULT_DEPTH,
):
    arg_type = synth_type(man, r, ctx)
    f = synth_term(
        man,
        r,
        ctx,
        AbstractionType(ctx.fresh_var(), arg_type, ty),
        d - 1,
        avoid_eta=True,
    )
    arg = synth_term(man, r, ctx, arg_type, d - 1, anf=True)
    return Application(f, arg)


def synth_abs(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: AbstractionType,
    d: int = 1,
):
    name = ty.var_name if ctx.type_of(ty.var_name) is None else ctx.fresh_var()
    e = synth_term(man, r, ctx.with_var(name, ty.var_type), ty.type, d - 1)
    return Abstraction(name, e)


def synth_let(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = 1,
):
    name = ctx.fresh_var()
    rty = synth_type(man, r, ctx)
    e1 = synth_term(man, r, ctx, rty, d - 1)
    e2 = synth_term(man, r, ctx.with_var(name, rty), ty, d - 1)
    return Rec(name, rty, e1, e2)


def synth_if(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = 1,
):
    cond = synth_term(man, r, ctx, t_bool, d - 1, anf=True)
    then = synth_term(man, r, ctx, ty, d - 1)
    otherwise = synth_term(man, r, ctx, ty, d - 1)
    return If(cond, then, otherwise)


def is_tail_of(ctx: TypingContext, a: Type, b: Type):
    while args_size_of_type(b) > args_size_of_type(a):
        pass

    if is_subtype(ctx, a, b):
        return True
    elif isinstance(a, AbstractionType) and args_size_of_type(a):
        return is_tail_of(ctx, a.type, b)
    else:
        return False


def synth_app_directed(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: AbstractionType,
    d: int = 1,
):
    options = [(n, v) for (n, v) in ctx.vars() if is_tail_of(ctx, ty, v)]
    assert options
    # TODO: Finish special synthesis
    return True


NOFILTER = True


def synth_term(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = DEFAULT_DEPTH,
    anf: bool = False,
    avoid_eta=False,
) -> Term:
    assert d >= 0
    b = base(ty)
    candidate_generators = []

    def go_lit():
        return synth_literal(man, r, ctx, ty, d)

    def go_var():
        return synth_var(man, r, ctx, ty, d)

    def go_app():
        return synth_app(man, r, ctx, ty, d)

    def go_abs():
        return synth_abs(man, r, ctx, ty, d)

    def go_let():
        return synth_let(man, r, ctx, ty, d)

    def go_if():
        return synth_if(man, r, ctx, ty, d)

    if (b == t_int or b == t_bool) and man.allow_lit(ctx, ty, d):
        candidate_generators.append(go_lit)

    if man.allow_var(ctx, ty, d):
        candidate_generators.append(go_var)

    if d > 0 and not anf and man.allow_app(ctx, ty, d):
        candidate_generators.append(go_app)
    if d > 0 and not anf and man.allow_abs(ctx, ty, d, go_var in candidate_generators, avoid_eta):
        if isinstance(ty, AbstractionType):
            candidate_generators.append(go_abs)
        candidate_generators.append(go_let)
        candidate_generators.append(go_if)
    if candidate_generators:
        while man.budget > 0:
            man.checkpoint()
            try:
                t = man.choose_rule(r, candidate_generators, d)
                if t:
                    return t
            except NoMoreBudget:
                pass
            man.undo_choice()
    raise NoMoreBudget()
