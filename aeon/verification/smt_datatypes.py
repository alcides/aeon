"""SMT reflection of Aeon inductive types as Z3 algebraic datatypes.

LiquidHaskell's ``--exact-data-cons`` / refinement-reflection path exposes ADT
constructors, recognisers, and field selectors in the logic so refinements can
reason about ``Nil`` / ``Cons`` structurally. Aeon previously modelled every
user-builtin ``TypeConstructor`` as an *uninterpreted* Z3 sort
(``DeclareSort``) with free constructor constants and a post-hoc ``Distinct``
axiom — enough for equality of opaque values, but not for constructing
``List.nil`` inside a VC (the Contata ``List_nil`` ``KeyError``).

This module builds a **monomorphic Z3 ``Datatype``** per inductive
instantiation (e.g. ``List Int`` → sort ``List_Int`` with constructors
``nil`` / ``cons``), keyed off :mod:`aeon.verification.constructor_registry`
(populated by ``expand_inductive_decls``). Field skeletons use:

* ``#i`` — the *i*-th type argument of the instantiation;
* the inductive's own name — a recursive occurrence of the datatype;
* a builtin (``Int``, ``Bool``, …) or another type constructor name.

Constructor symbols are then available to :func:`aeon.verification.smt.translate_liq`
by base name (``List_nil``, ``List_cons``, …), independent of binder ids.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Optional

from z3 import Datatype, DatatypeSortRef
from z3.z3 import BoolSort, IntSort, RealSort, StringSort, SortRef

from aeon.core.types import Type, TypeConstructor, RefinedType
from aeon.utils.name import Name
from aeon.verification.constructor_registry import (
    get_constructor_fields,
    get_constructor_order,
    get_type_param_count,
)

# Mangling must match ``aeon.verification.smt._mangle_sort_name``.
_SUPERSCRIPTS = "⁰¹²³⁴⁵⁶⁷⁸⁹"


@dataclass
class DatatypeInfo:
    """A built monomorphic inductive sort and its constructor/accessor map."""

    sort: DatatypeSortRef
    sort_name: str
    type_name: str
    # Prefixed Aeon names (``List_nil``) → Z3 constructor (nullary const or fun).
    constructors: dict[str, Any]
    # Prefixed Aeon names → short Z3 constructor name (``nil``).
    short_names: dict[str, str]


# sort mangled name → info
_datatype_cache: dict[str, DatatypeInfo] = {}
# Aeon constructor base name → list of (sort_name, z3_ctor) for disambiguation
_ctors_by_aeon_name: dict[str, list[tuple[str, Any]]] = {}
# sorts currently under construction (guard recursion through get_sort)
_building: set[str] = set()


def clear_datatype_cache() -> None:
    _datatype_cache.clear()
    _ctors_by_aeon_name.clear()
    _building.clear()


def strip_binder_id(name: str) -> str:
    """Drop trailing unicode-superscript binder ids (``List_nil⁷`` → ``List_nil``)."""
    return name.rstrip(_SUPERSCRIPTS)


def constructor_logical_name(name: str) -> str:
    """Map a possibly specialised SMT symbol back to the registry constructor name.

    ``_specialize_liquid_term`` emits twins like ``List_cons__spec__a__1063``;
    exact-data-cons reflection keys constructors as ``List_cons``. Binder ids and
    ``__spec__…`` suffixes are stripped so liquid apps resolve to the Z3
    datatype constructor.
    """
    base = strip_binder_id(name)
    if "__spec__" in base:
        base = base.split("__spec__", 1)[0]
    return base


def is_registered_inductive(type_name: str) -> bool:
    return get_constructor_order(type_name) is not None


def _unrefine(ty: Type) -> Type:
    while isinstance(ty, RefinedType):
        ty = ty.type
    return ty


def _builtin_sort(name: str) -> Optional[SortRef]:
    return {
        "Int": IntSort(),
        "Bool": BoolSort(),
        "Float": RealSort(),
        "String": StringSort(),
        "Unit": None,  # handled by caller via get_sort
        "Top": IntSort(),
    }.get(name)


def _short_ctor_name(type_name: str, prefixed: str) -> str:
    prefix = f"{type_name}_"
    if prefixed.startswith(prefix):
        return prefixed[len(prefix) :]
    return prefixed


def _inductive_sort_name(type_name: str, args: list[Type], mangle: Callable[[Type], str]) -> str:
    """Monomorphic sort name for a registered inductive, **id-free** on the head.

    The constructor registry keys types by ``name.name`` (no binder id). Using
    ``_mangle_sort_name`` on ``TypeConstructor(Name("List", 1023), …)`` would
    produce ``List__1023_Int``, while a VC binder typed as ``List`` with a
    different id would miss the datatype. Logical names keep one Z3 sort per
    instantiation (LH-style monomorphisation).
    """
    if not args:
        return type_name
    parts: list[str] = [type_name]
    for a in args:
        a = _unrefine(a)
        if (
            isinstance(a, TypeConstructor)
            and not a.args
            and a.name.name
            in {
                "Int",
                "Bool",
                "Float",
                "String",
                "Unit",
                "Top",
            }
        ):
            parts.append(a.name.name)
        else:
            parts.append(mangle(a))
    return "_".join(parts)


def try_build_inductive_sort(
    base: TypeConstructor,
    get_sort: Callable[[Type], SortRef],
    mangle: Callable[[Type], str],
) -> Optional[DatatypeInfo]:
    """Build (or fetch) a Z3 datatype for ``base`` when it is a registered inductive.

    Returns ``None`` for non-inductives so the caller can fall back to
    ``DeclareSort``. ``get_sort`` / ``mangle`` are injected to avoid an import
    cycle with :mod:`aeon.verification.smt`.
    """
    type_name = base.name.name
    order = get_constructor_order(type_name)
    if order is None:
        return None

    # Enforce arity: ``List`` expects 1 type argument.
    nparams = get_type_param_count(type_name)
    args = [_unrefine(a) for a in base.args]
    if nparams and len(args) != nparams:
        # Under-applied polymorphic constructor — keep uninterpreted.
        return None

    sname = _inductive_sort_name(type_name, args, mangle)
    cached = _datatype_cache.get(sname)
    if cached is not None:
        return cached
    if sname in _building:
        # Recursion through another field while this datatype is open — the
        # Z3 ``Datatype`` object itself is the recursive placeholder.
        return None

    _building.add(sname)
    try:
        dt = Datatype(sname)
        field_names_per_ctor: dict[str, list[str]] = {}

        for prefixed in order:
            fields = get_constructor_fields(prefixed) or []
            z3_fields: list[tuple[str, Any]] = []
            fnames: list[str] = []
            for i, skel in enumerate(fields):
                fname = f"{_short_ctor_name(type_name, prefixed)}_{i}"
                fnames.append(fname)
                if skel.startswith("#"):
                    idx = int(skel[1:])
                    if idx < 0 or idx >= len(args):
                        raise ValueError(f"field skeleton {skel} out of range for {base}")
                    z3_fields.append((fname, get_sort(args[idx])))
                elif skel == type_name:
                    # Recursive occurrence of the inductive being defined.
                    z3_fields.append((fname, dt))
                else:
                    builtin = _builtin_sort(skel)
                    if builtin is not None:
                        z3_fields.append((fname, builtin))
                    elif skel == "Unit":
                        z3_fields.append((fname, get_sort(TypeConstructor(Name("Unit", 0)))))
                    else:
                        # Another nominal type (possibly inductive). Build it
                        # as a fully-applied nullary constructor name.
                        z3_fields.append((fname, get_sort(TypeConstructor(Name(skel, 0)))))
            short = _short_ctor_name(type_name, prefixed)
            if z3_fields:
                dt.declare(short, *z3_fields)
            else:
                dt.declare(short)
            field_names_per_ctor[prefixed] = fnames

        created: DatatypeSortRef = dt.create()
        constructors: dict[str, Any] = {}
        short_names: dict[str, str] = {}
        for prefixed in order:
            short = _short_ctor_name(type_name, prefixed)
            z3_ctor = getattr(created, short)
            constructors[prefixed] = z3_ctor
            short_names[prefixed] = short
            _ctors_by_aeon_name.setdefault(prefixed, []).append((sname, z3_ctor))

        info = DatatypeInfo(
            sort=created,
            sort_name=sname,
            type_name=type_name,
            constructors=constructors,
            short_names=short_names,
        )
        _datatype_cache[sname] = info
        return info
    finally:
        _building.discard(sname)


def lookup_constructor(aeon_name: str, preferred_sort: str | None = None) -> Any | None:
    """Resolve an Aeon constructor base name to a Z3 constructor symbol.

    If several monomorphic instantiations exist (``List_nil`` at ``List_Int``
    and ``List_Bool``), ``preferred_sort`` selects one; otherwise the sole
    entry is returned, or ``None`` if ambiguous / missing. Accepts specialised
    twin names (``List_cons__spec__…``).
    """
    base = constructor_logical_name(aeon_name)
    entries = _ctors_by_aeon_name.get(base)
    if not entries:
        return None
    if preferred_sort is not None:
        for sname, ctor in entries:
            if sname == preferred_sort:
                return ctor
    if len(entries) == 1:
        return entries[0][1]
    # Prefer an Int instantiation when ambiguous (common for Contata / List Int).
    for sname, ctor in entries:
        if sname.endswith("_Int") or sname == "Int":
            return ctor
    return entries[0][1]


def is_datatype_constructor_name(aeon_name: str) -> bool:
    return constructor_logical_name(aeon_name) in _ctors_by_aeon_name


def constructors_for_env() -> dict[str, Any]:
    """Flat ``{List_nil: <z3>, List_cons: <z3>, …}`` for the SMT translation env.

    When the same constructor exists at several instantiations, the Int-ish
    (or first) one wins — binders with explicit ids in the VC still override
    via the normal variables/functions maps.
    """
    out: dict[str, Any] = {}
    for name, entries in _ctors_by_aeon_name.items():
        ctor = lookup_constructor(name)
        if ctor is not None:
            out[name] = ctor
    return out
