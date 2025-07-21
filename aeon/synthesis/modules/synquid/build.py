from itertools import count, takewhile
import itertools
from typing import Callable

from aeon.core.terms import Annotation, Application, If, Literal, TypeApplication, Var
from aeon.core.types import AbstractionType, RefinedType, Type, TypeConstructor, TypePolymorphism, TypeVar
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def monomorfic(t: Type, typing_ctx: TypingContext, t_l: dict[Name, Type]):
    match t:
        case TypePolymorphism(var_name, _, var_body):
            for t in [
                t
                for n, t in typing_ctx.concrete_vars()
                if isinstance(t, TypeConstructor) and t != TypeConstructor(Name("Unit", 0))
            ]:
                t_l[var_name] = t
                for result in monomorfic(var_body, typing_ctx, t_l):
                    yield result
        case AbstractionType(var_name, var_type, typ):
            for in_type in monomorfic(var_type, typing_ctx, t_l):
                for body in monomorfic(typ, typing_ctx, t_l):
                    yield AbstractionType(var_name, in_type, body)
        case TypeVar(var_name):
            yield t_l[var_name]
        case _:
            yield t


def uncurry(typ: Type):
    match typ:
        case TypeConstructor():
            return [], typ
        case TypeVar(var_name):
            return [], TypeConstructor(var_name, [])
        case AbstractionType(_, _, _):
            t = typ
            params = []
            while isinstance(t, AbstractionType):
                if isinstance(t.var_type, (TypeConstructor, AbstractionType)):
                    params.append(t.var_type)
                else:
                    assert isinstance(t.var_type, RefinedType)
                    if isinstance(t.var_type.type, TypeConstructor):
                        params.append(t.var_type.type)
                if not isinstance(t.type, AbstractionType):
                    break
                t = t.type

            if isinstance(t.type, TypeConstructor):
                return params, t.type
            else:
                assert isinstance(t.type, RefinedType)
                return params, t.type.type
        case RefinedType():
            return [], typ.type
        case _:
            print(type(typ))
            assert False, f"Unsupported {typ}"


def frange(start, stop, step):
    return takewhile(lambda x: x < stop, count(start, step))


def closing(elems: tuple, typ: TypeConstructor):
    if len(elems) == 1:
        return TypeApplication(elems[0], typ)
    else:
        return Application(closing(elems[:-1], typ), elems[-1])


def synthes_memory(ctx: TypingContext, level: int, ret_t: Type, skip: Callable[[Name], bool], mem: dict):
    if (ctx, level, ret_t) in mem:
        yield from mem[(ctx, level, ret_t)]
    else:
        mem[(ctx, level, ret_t)] = []
        try:
            for item in synthes(ctx, level, ret_t, skip, mem):
                mem[(ctx, level, ret_t)].append(item)
                yield item
        except NotImplementedError:
            yield from []


def match_type(t1: Type, t2: Type):
    if t1 == t2:
        return True
    elif type(t1) is type(t2):
        return False
    elif isinstance(t1, AbstractionType) and isinstance(t2, AbstractionType):
        return match_type(t1.var_type, t2.var_type) and match_type(t1.type, t2.type)
    else:
        return False


def synthes(ctx: TypingContext, level: int, ret_t: Type, skip: Callable[[Name], bool], mem: dict):
    if level == 0:
        if isinstance(ret_t, AbstractionType):
            for name, _ in [
                (n, t) for n, t in ctx.concrete_vars() if isinstance(t, AbstractionType) and match_type(t, ret_t)
            ]:
                yield Var(name)
        else:
            assert isinstance(ret_t, TypeConstructor)
            for name, _ in [
                (n, t) for n, t in ctx.concrete_vars() if isinstance(t, TypeConstructor) and match_type(t, ret_t)
            ]:
                yield Var(name)
        match ret_t:
            case TypeConstructor(Name("Bool", 0)):
                yield from [Literal(True, ret_t), Literal(False, ret_t)]
            case TypeConstructor(Name("Int", 0)):
                yield from [Literal(value, ret_t) for value in range(-100, 100)]
            case TypeConstructor(Name("Float", 0)):
                yield from [Literal(value, ret_t) for value in frange(-100.0, 100.0, 0.00001)]
            case TypeConstructor(Name("String", 0)):
                raise NotImplementedError
            case _:
                raise NotImplementedError
    elif level >= 1:
        for name, typ in [
            (n, ty) for n, ty in ctx.concrete_vars() if not isinstance(ty, TypeConstructor) and not skip(n)
        ]:
            for candidate in monomorfic(typ, ctx, {}) if isinstance(typ, TypePolymorphism) else [typ]:
                params_t, t = uncurry(candidate)
                if t != ret_t:
                    continue
                params = [
                    synthes_memory(ctx, level - 1, i, skip, mem)
                    if isinstance(i, TypeConstructor)
                    else synthes_memory(ctx, 0, i, skip, mem)
                    for i in params_t
                ]
                params.insert(0, [Var(name)])
                for i in itertools.product(*params):
                    a = closing(i, t)
                    yield a
        # if
        cond = synthes_memory(ctx, level - 1, TypeConstructor(Name("Bool", 0)), skip, mem)
        then = synthes_memory(ctx, level - 1, ret_t, skip, mem)
        otherwise = synthes_memory(ctx, level - 1, ret_t, skip, mem)
        for cand in itertools.product(*[cond, then, otherwise]):
            if isinstance(cand[0], If):
                break
            yield Annotation(If(cand[0], cand[1], cand[2]), ret_t)
