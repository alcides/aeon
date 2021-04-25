from aeon.core.liquid import LiquidLiteralBool
from aeon.core.pprint import pretty_print
from typing import ContextManager, Optional, List
from aeon.core.terms import Abstraction, Application, If, Let, Literal, Rec, Var, Term
from aeon.core.types import (
    AbstractionType,
    BaseType,
    RefinedType,
    Type,
    args_size_of_type,
    t_int,
    t_bool,
    base,
)
from aeon.synthesis.exceptions import NoMoreBudget
from aeon.synthesis.sources import RandomSource
from aeon.synthesis.choice_manager import ChoiceManager, DynamicProbManager
from aeon.synthesis.type_synthesis import synth_type
from aeon.typing.context import EmptyContext, TypeBinder, TypingContext, VariableBinder
from aeon.typing.typeinfer import check_type, is_subtype
from aeon.synthesis.smt_synthesis import smt_synth_int_lit

DEFAULT_DEPTH = 9


def synth_literal(
    man: ChoiceManager,
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = DEFAULT_DEPTH,
) -> Optional[Literal]:
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
            if check_type(ctx, k, ty):
                return k
            else:
                print("(d) does not typecheck", k, type(k), ty)
                man.undo_choice()
        raise NoMoreBudget()
    else:
        raise NoMoreBudget()


def vars_of_type(
    ctx: TypingContext, ty: Type, ictx: Optional[TypingContext] = None
) -> List[str]:
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


def any_var_of_type(
    ctx: TypingContext, ty: Type, ictx: Optional[TypingContext] = None
) -> bool:
    if ictx is None:
        return any_var_of_type(ctx, ty, ctx)
    if isinstance(ictx, EmptyContext):
        return False
    elif isinstance(ictx, VariableBinder):
        if is_subtype(ctx, ictx.type, ty):
            return True
        return any_var_of_type(ctx, ty, ictx.prev)
    elif isinstance(ictx, TypeBinder):
        return any_var_of_type(ctx, ty, ictx.prev)
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
    elif isinstance(a, AbstractionType) and args_size_of_type:
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
    pass


def steps_necessary_to_close(ctx: TypingContext, ty: Type):
    max_arrows = max([0] + [args_size_of_type(ty_) for (_, ty_) in ctx.vars()])
    arrows_ty = args_size_of_type(ty)
    d = max(arrows_ty - max_arrows, 0)
    return d


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

    if b == t_int or b == t_bool or NOFILTER:
        candidate_generators.append(go_lit)

    if any_var_of_type(ctx, ty) or NOFILTER:
        candidate_generators.append(go_var)

    if not anf and (d > 0 and NOFILTER) or (d > steps_necessary_to_close(ctx, ty) + 1):
        candidate_generators.append(go_app)
    if (d > 0 and NOFILTER) or (
        d > 0 and not anf and (not avoid_eta or go_var not in candidate_generators)
    ):
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
