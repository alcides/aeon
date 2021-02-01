from typing import Optional, List
from aeon.core.terms import Abstraction, Application, Literal, Var
from aeon.core.types import AbstractionType, BaseType, RefinedType, Type, t_int, t_bool
from aeon.synthesis.sources import RandomSource
from aeon.typing.context import EmptyContext, TypingContext, VariableBinder
from aeon.typing.typeinfer import check_type


def synth_literal(r: RandomSource, ctx: TypingContext, ty: Type) -> Optional[Literal]:
    print("syntlit", ty)
    if isinstance(ty, BaseType):
        if ty == t_int:
            return Literal(r.next_integer(), ty)
        elif ty == t_bool:
            return Literal(r.choose([True, False]), ty)
        else:
            assert False
    elif isinstance(ty, RefinedType):
        for _ in range(100):
            k = synth_literal(r, ctx, ty.type)
            if check_type(ctx, k, ty):
                return k
            else:
                return None
        return None
    else:
        return None


from aeon.verification.sub import sub
from aeon.typing.entailment import entailment


def is_subtype(ctx: TypingContext, subt: Type, supt: Type):
    c = sub(subt, supt)
    return entailment(ctx, c)


def vars_of_type(
    ctx: TypingContext, ty: Type, ictx: Optional[TypingContext] = None
) -> List[str]:
    if not ictx:
        return vars_of_type(ctx, ty, ctx)

    if isinstance(ictx, EmptyContext):
        return []
    elif isinstance(ictx, VariableBinder):
        rest = vars_of_type(ctx, ty, ictx.prev)
        if is_subtype(ctx, ictx.type, ty):
            return [ictx.name] + rest
        else:
            return rest
    else:
        print(ictx, type(ictx))
        assert False


def synth_var(r: RandomSource, ctx: TypingContext, ty: Type):
    candidates = vars_of_type(ctx, ty)
    if candidates:
        return Var(r.choose(candidates))
    return None


def extract_base_type(ty: Type):
    if isinstance(ty, RefinedType):
        return ty.type
    else:
        return ty


def synth_type(r: RandomSource):
    return r.choose([t_int, t_bool])


def synth_app(r: RandomSource, ctx: TypingContext, ty: Type):
    arg_type = synth_type(r)
    f = synth_term(r, ctx, AbstractionType("k", arg_type, ty))
    arg = synth_term(r, ctx, arg_type)
    return Application(f, arg)


def synth_abs(r: RandomSource, ctx: TypingContext, ty: AbstractionType):
    name = ty.var_name if ctx.type_of(ty.var_name) is None else ctx.fresh_var()
    e = synth_term(r, ctx.with_var(name, ty.var_type), ty.type)
    return Abstraction(name, e)


def synth_term(r: RandomSource, ctx: TypingContext, ty: Type):
    b = extract_base_type(ty)

    candidate_generators = []

    if b == t_int or b == t_bool:
        candidate_generators.append(lambda: synth_literal(r, ctx, ty))

    candidate_generators.append(lambda: synth_var(r, ctx, ty))

    candidate_generators.append(lambda: synth_app(r, ctx, ty))

    if isinstance(ty, AbstractionType):
        candidate_generators.append(lambda: synth_abs(r, ctx, ty))

    for _ in range(100):
        f = r.choose(candidate_generators)
        t = f()
        if t:
            return t
