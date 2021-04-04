from aeon.core.pprint import pretty_print
from typing import Optional, List
from aeon.core.terms import Abstraction, Application, Literal, Var, Term
from aeon.core.types import (
    AbstractionType,
    BaseType,
    RefinedType,
    Type,
    t_int,
    t_bool,
    base,
)
from aeon.synthesis.exceptions import NoMoreBudget
from aeon.synthesis.sources import RandomSource
from aeon.synthesis.type_synthesis import synth_type
from aeon.typing.context import EmptyContext, TypeBinder, TypingContext, VariableBinder
from aeon.typing.typeinfer import check_type
from aeon.synthesis.smt_synthesis import smt_synth_int_lit

DEFAULT_DEPTH = 9
DEFAULT_CHECK_TRIES = 100


def synth_literal(
    r: RandomSource, ctx: TypingContext, ty: Type, d: int = DEFAULT_DEPTH
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
        for _ in range(DEFAULT_CHECK_TRIES):
            k = synth_literal(r, ctx, ty.type)
            if check_type(ctx, k, ty):
                return k
            else:
                print("does not typecheck", k, type(k), ty)
        raise NoMoreBudget()
    else:
        raise NoMoreBudget()


from aeon.verification.sub import sub
from aeon.typing.entailment import entailment


def is_subtype(ctx: TypingContext, subt: Type, supt: Type):
    c = sub(subt, supt)
    return entailment(ctx, c)


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


def synth_var(r: RandomSource, ctx: TypingContext, ty: Type, d: int = DEFAULT_DEPTH):
    candidates = vars_of_type(ctx, ty)
    if candidates:
        return Var(r.choose(candidates))
    raise NoMoreBudget()


def synth_app(r: RandomSource, ctx: TypingContext, ty: Type, d: int = DEFAULT_DEPTH):
    arg_type = synth_type(r, ctx)
    print("CHOSEN TYPE:", arg_type)
    f = synth_term(r, ctx, AbstractionType(ctx.fresh_var(), arg_type, ty), d - 1)
    arg = synth_term(r, ctx, arg_type, d - 1, anf=True)
    return Application(f, arg)


def synth_abs(r: RandomSource, ctx: TypingContext, ty: AbstractionType, d: int = 1):
    name = ty.var_name if ctx.type_of(ty.var_name) is None else ctx.fresh_var()
    e = synth_term(r, ctx.with_var(name, ty.var_type), ty.type, d - 1)
    return Abstraction(name, e)


def any_var_of_type(ctx: TypingContext, ty: TypingContext):
    if isinstance(ctx, EmptyContext):
        return False
    elif isinstance(ctx, VariableBinder):
        if check_type(ctx, Var(ctx.name), ty):
            return True
        return any_var_of_type(ctx.prev, ty)
    elif isinstance(ctx, TypeBinder):
        return any_var_of_type(ctx.prev, ty)


def synth_term(
    r: RandomSource,
    ctx: TypingContext,
    ty: Type,
    d: int = DEFAULT_DEPTH,
    anf: bool = False,
) -> Term:
    b = base(ty)
    candidate_generators = []
    print("synthing", ty)

    def go_lit():
        return synth_literal(r, ctx, ty, d)

    def go_var():
        return synth_var(r, ctx, ty, d)

    def go_app():
        return synth_app(r, ctx, ty, d)

    def go_abs():
        return synth_abs(r, ctx, ty, d)

    if b == t_int or b == t_bool:
        candidate_generators.append(go_lit)
    if vars_of_type(ctx, ty):
        candidate_generators.append(go_var)

    if d > 0 and not anf:
        candidate_generators.append(go_app)
        if isinstance(ty, AbstractionType):
            candidate_generators.append(go_abs)
    if candidate_generators:
        for _ in range(DEFAULT_CHECK_TRIES):
            f = r.choose(candidate_generators)
            print("RULE CHOSEN", f, candidate_generators)
            try:
                t = f()
                if t:
                    return t
                else:
                    print("Failed to get", ty, len(candidate_generators))
            except RecursionError:
                raise NoMoreBudget()

    print("D", candidate_generators)
    raise NoMoreBudget()
