"""Indexed grammar component library for type-directed search.

Built once per ``(TypingContext, skip)``: monomorphized Instantiables are
bucketed by return-base and first-argument-base so backward/forward application
and close tactics become map lookups instead of full-context scans.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass

from aeon.core.terms import Term, Var
from aeon.core.types import (
    AbstractionType,
    RefinementPolymorphism,
    Type,
    TypePolymorphism,
)
from aeon.synthesis.modules.tdsyn.helpers import (
    base_type_of,
    get_return_type,
    monomorphize,
)
from aeon.typechecking.context import TypingContext
from aeon.utils.location import SynthesizedLocation
from aeon.utils.name import Name

_loc = SynthesizedLocation("tdsyn")

# Bucket for function/value types whose relevant position is not a base constructor
# (e.g. higher-order parameters). Always consulted alongside a concrete key.
_OTHER = "*"

FunEntry = tuple[Term, AbstractionType]
ValueEntry = tuple[Term, Type]

_library_cache: dict[int, "ComponentLibrary"] = {}


def clear_component_library_cache() -> None:
    _library_cache.clear()


def _base_key(ty: Type) -> str:
    bt = base_type_of(ty)
    return bt.name.name if bt is not None else _OTHER


@dataclass(frozen=True)
class ComponentLibrary:
    """Monomorphized functions and closeable values, indexed by base constructor."""

    functions: tuple[FunEntry, ...]
    by_return: dict[str, tuple[FunEntry, ...]]
    by_first_arg: dict[str, tuple[FunEntry, ...]]
    values: tuple[ValueEntry, ...]
    by_value_base: dict[str, tuple[ValueEntry, ...]]

    def functions_returning(self, goal: Type) -> Sequence[FunEntry]:
        """Functions whose final return base matches ``goal`` (plus non-base returns)."""
        key = _base_key(goal)
        if key == _OTHER:
            return self.functions
        return _merge_buckets(self.by_return, key)

    def functions_accepting(self, arg_ty: Type) -> Sequence[FunEntry]:
        """Functions whose first parameter base matches ``arg_ty`` (plus non-base params)."""
        key = _base_key(arg_ty)
        if key == _OTHER:
            return self.functions
        return _merge_buckets(self.by_first_arg, key)

    def values_matching(self, goal: Type) -> Sequence[ValueEntry]:
        """Closeable non-function values whose base matches ``goal``."""
        key = _base_key(goal)
        if key == _OTHER:
            return self.values
        return _merge_buckets(self.by_value_base, key)


def _merge_buckets(index: dict[str, tuple], key: str) -> tuple:
    primary = index.get(key, ())
    other = index.get(_OTHER, ()) if key != _OTHER else ()
    if not other:
        return primary
    if not primary:
        return other
    return primary + other


def get_component_library(
    ctx: TypingContext,
    skip: Callable[[Name], bool],
) -> ComponentLibrary:
    """Return (and memoize) the indexed library for ``ctx``.

    Cached by ``id(ctx)`` only. ``skip`` must stay stable for the lifetime of
    the cache entry — synthesis runs call :func:`clear_component_library_cache`
    (via ``clear_tdsyn_caches``) before search so a fresh skip is always used.
    Keying on ``id(skip)`` caused flaky unit tests when GC reused addresses.
    """
    key = id(ctx)
    cached = _library_cache.get(key)
    if cached is not None:
        return cached
    library = _build_library(ctx, skip)
    _library_cache[key] = library
    return library


def _build_library(ctx: TypingContext, skip: Callable[[Name], bool]) -> ComponentLibrary:
    functions: list[FunEntry] = []
    values: list[ValueEntry] = []

    for name, ty in ctx.vars():
        if skip(name):
            continue
        if isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            for term, mono_ty in monomorphize(name, ty, ctx):
                if isinstance(mono_ty, AbstractionType):
                    functions.append((term, mono_ty))
                else:
                    values.append((term, mono_ty))
        elif isinstance(ty, AbstractionType):
            functions.append((Var(name, _loc), ty))
        else:
            values.append((Var(name, _loc), ty))

    by_return: dict[str, list[FunEntry]] = defaultdict(list)
    by_first_arg: dict[str, list[FunEntry]] = defaultdict(list)
    for fun_entry in functions:
        _, f_type = fun_entry
        by_return[_base_key(get_return_type(f_type))].append(fun_entry)
        by_first_arg[_base_key(f_type.var_type)].append(fun_entry)

    by_value: dict[str, list[ValueEntry]] = defaultdict(list)
    for value_entry in values:
        by_value[_base_key(value_entry[1])].append(value_entry)

    return ComponentLibrary(
        functions=tuple(functions),
        by_return={k: tuple(v) for k, v in by_return.items()},
        by_first_arg={k: tuple(v) for k, v in by_first_arg.items()},
        values=tuple(values),
        by_value_base={k: tuple(v) for k, v in by_value.items()},
    )


def iter_concrete_vars(ctx: TypingContext, skip: Callable[[Name], bool]) -> Iterable[tuple[Name, Type]]:
    """Non-function variables in ``ctx`` (used when a full scan is still needed)."""
    for name, var_type in ctx.vars():
        if skip(name):
            continue
        if isinstance(var_type, (AbstractionType, TypePolymorphism, RefinementPolymorphism)):
            continue
        yield name, var_type
