from dataclasses import dataclass
from functools import lru_cache
from itertools import count, takewhile
import itertools
from typing import Any, Callable
import types

from aeon.core.terms import Abstraction, Application, Literal, TypeApplication, Var
from aeon.core.types import AbstractionType, Type, TypeConstructor, TypePolymorphism, TypeVar
from aeon.core.types import t_bool, t_int, t_float, t_string, t_unit
from aeon.typechecking.context import TypingContext
from aeon.utils.name import Name

def extract_context(ctx: TypingContext, synth_fun_type: Type):
    def skip(name: Name) -> bool:
        if name.name.startswith("__internal__"):
            return True
        elif name.name in ["native", "native_import", "print"]:
            return True
        else:
            return False
    ctx_vars = [(var_name, ty) for (var_name, ty) in ctx.concrete_vars() if not skip(var_name)]
    base_types = set([t_bool, t_float, t_int, t_string]) | set([synth_fun_type])
    return ctx_vars + list(base_types)

def monomorfic(t: Type, typing_ctx:TypingContext, t_l:dict[Name, Type]):
    match t:
        case TypePolymorphism(var_name, _, var_body):
            for t in [t for n,t in typing_ctx.concrete_vars() if isinstance(t,TypeConstructor)]:
                t_l[var_name] = t
                for result in monomorfic(var_body, typing_ctx, t_l):
                    yield result
        case AbstractionType(var_name, var_type, typ):
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
                params.append(t.var_type)
                t = t.type
            return params, t  
        case TypePolymorphism(var_name, _, var_body):
            t = var_body
            params = [TypeConstructor(var_name, [])]
            while isinstance(t, AbstractionType):
                params.append(t.var_type)
                t = t.type
            return params, t
        case _:
            print(type(typ))
            assert False, f"Unsupported {typ}"

def frange(start, stop, step):
    return takewhile(lambda x: x < stop, count(start, step))

def closing(elems : list, typ: TypeConstructor):
    if len(elems) == 1:
        return TypeApplication(elems[0], typ)
    else:
        return Application(closing(elems[:-1], typ), elems[-1])


#@lru_cache
def synthes(ctx:TypingContext, level: int, ret_t: Type, skip: Callable[[Name], bool]):
    if level == 0:
        for name, typ in [(n,t) for n,t in ctx.concrete_vars() if isinstance(t,TypeConstructor) and t == ret_t]:
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
        for name, typ in [(n,t) for n,t in ctx.concrete_vars() if not isinstance(t,TypeConstructor) and not skip(n)]:
            for candidate in (monomorfic(typ, ctx, {}) if isinstance(typ, TypePolymorphism) else [typ]):
                params_t, t = uncurry(candidate)
                if t != ret_t:
                    continue
                params = [synthes(ctx, level-1, i, skip) for i in params_t]
                params.insert(0, [Var(name)])
                for i in itertools.product(*params):
                    a =closing(i, t)
                    yield  a
        


