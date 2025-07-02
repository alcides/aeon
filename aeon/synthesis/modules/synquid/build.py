from itertools import count, takewhile
import itertools
from typing import Callable

from aeon.core.terms import Application, Literal, TypeApplication, Var
from aeon.core.types import AbstractionType, Type, TypeConstructor, TypePolymorphism, TypeVar
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name


def monomorfic(t: Type, typing_ctx: TypingContext, t_l: dict[Name, Type]):
    match t:
        case TypePolymorphism(var_name, _, var_body):
            for t in [t for n, t in typing_ctx.concrete_vars() if isinstance(t, TypeConstructor)]:
                t_l[var_name] = t
                for result in monomorfic(var_body, typing_ctx, t_l):
                    yield result
        case AbstractionType(var_name, var_type, typ):
            assert isinstance(var_type, (TypeVar))
            for body in monomorfic(typ, typing_ctx, t_l):
                yield AbstractionType(var_name, t_l[var_type.name], body)
        case TypeVar(var_name):
            yield t_l[var_name]
        case _:
            yield t


def uncurry(typ: Type) -> tuple[list[TypeConstructor], TypeConstructor]:
    match typ:
        case TypeConstructor():
            return [], typ
        case TypeVar(var_name):
            return [], TypeConstructor(var_name, [])
        case AbstractionType(_, _, _):
            t = typ
            params = []
            while isinstance(t, AbstractionType):
                assert isinstance(t.var_type, TypeConstructor)
                params.append(t.var_type)
                if not isinstance(t.type, AbstractionType):
                    break
                t = t.type
            assert isinstance(t.type, TypeConstructor)
            return params, t.type
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
        for item in synthes(ctx, level, ret_t, skip, mem):
            mem[(ctx, level, ret_t)].append(item)
            yield item


def synthes(ctx: TypingContext, level: int, ret_t: Type, skip: Callable[[Name], bool], mem: dict):
    if level == 0:
        for name, _ in [(n, t) for n, t in ctx.concrete_vars() if isinstance(t, TypeConstructor) and t == ret_t]:
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
                params = [synthes_memory(ctx, level - 1, i, skip, mem) for i in params_t]
                params.insert(0, [Var(name)])
                for i in itertools.product(*params):
                    a = closing(i, t)
                    yield a
