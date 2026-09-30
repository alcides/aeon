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

from z3 import Datatype, DatatypeSortRef, RecFunction, RecAddDefinition, Const, If, IntVal
from z3.z3 import BoolSort, IntSort, RealSort, StringSort, SortRef

from aeon.core.types import Type, TypeConstructor, RefinedType
from aeon.utils.name import Name
from aeon.verification.constructor_registry import (
    get_constructor_fields,
    get_constructor_order,
    get_measures,
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
    # Aeon measure base names (``List_size``) → Z3 ``RecFunction``.
    measures: dict[str, Any]


# sort mangled name → info
_datatype_cache: dict[str, DatatypeInfo] = {}
# Aeon constructor base name → list of (sort_name, z3_ctor) for disambiguation
_ctors_by_aeon_name: dict[str, list[tuple[str, Any]]] = {}
# Aeon measure base name → list of (sort_name, RecFunction)
_measures_by_aeon_name: dict[str, list[tuple[str, Any]]] = {}
# sorts currently under construction (guard recursion through get_sort)
_building: set[str] = set()
# Z3 keeps RecFunction decls for the process lifetime; freshen names on rebuild.
_measure_rec_fresh: int = 0


def clear_datatype_cache() -> None:
    global _measure_rec_fresh
    _datatype_cache.clear()
    _ctors_by_aeon_name.clear()
    _measures_by_aeon_name.clear()
    _building.clear()
    _measure_rec_fresh += 1


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


def _build_measure_recfunction(
    info_sort: DatatypeSortRef,
    sort_name: str,
    type_name: str,
    order: list[str],
    measure_name: str,
) -> Any:
    """LH-style structural measure: nullary → 0, else 1 + Σ measure(recursive fields)."""
    # Include ``_measure_rec_fresh`` so a cache clear + rebuild does not collide
    # with a RecFunction still resident in the process-wide Z3 context.
    rec = RecFunction(f"{sort_name}__{measure_name}__{_measure_rec_fresh}", info_sort, IntSort())
    x = Const(f"{sort_name}_{measure_name}_{_measure_rec_fresh}_x", info_sort)
    cases: list[tuple[Any, Any]] = []
    for i, prefixed in enumerate(order):
        fields = get_constructor_fields(prefixed) or []
        recog = info_sort.recognizer(i)
        if not fields:
            cases.append((recog, IntVal(0)))
            continue
        rec_sum: Any | None = None
        for j, skel in enumerate(fields):
            if skel != type_name:
                continue
            acc = info_sort.accessor(i, j)
            term = rec(acc(x))
            rec_sum = term if rec_sum is None else rec_sum + term
        if rec_sum is None:
            cases.append((recog, IntVal(1)))
        else:
            cases.append((recog, IntVal(1) + rec_sum))
    body: Any = IntVal(0)
    for recog, val in reversed(cases):
        body = If(recog(x), val, body)
    RecAddDefinition(rec, [x], body)
    return rec


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

        # LH measures: recursive definitions over the datatype (size nil = 0,
        # size (cons h t) = 1 + size t, …). One RecFunction per sort, aliased
        # under every registered measure name (``size`` and ``List_size``).
        measure_funs: dict[str, Any] = {}
        measure_names = get_measures(type_name)
        if measure_names:
            canonical = next(
                (n for n in measure_names if n.startswith(f"{type_name}_")),
                measure_names[0],
            )
            rec = _build_measure_recfunction(created, sname, type_name, order, canonical)
            for mname in measure_names:
                measure_funs[mname] = rec
                _measures_by_aeon_name.setdefault(mname, []).append((sname, rec))

        info = DatatypeInfo(
            sort=created,
            sort_name=sname,
            type_name=type_name,
            constructors=constructors,
            short_names=short_names,
            measures=measure_funs,
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


def lookup_measure(aeon_name: str, preferred_sort: str | None = None) -> Any | None:
    """Resolve an Aeon measure (``List_size``) to its Z3 ``RecFunction``.

    Same disambiguation rules as :func:`lookup_constructor`.
    """
    base = constructor_logical_name(aeon_name)
    entries = _measures_by_aeon_name.get(base)
    if not entries:
        return None
    if preferred_sort is not None:
        for sname, fun in entries:
            if sname == preferred_sort:
                return fun
    if len(entries) == 1:
        return entries[0][1]
    for sname, fun in entries:
        if sname.endswith("_Int") or sname == "Int":
            return fun
    return entries[0][1]


def measures_for_env() -> dict[str, Any]:
    """Flat ``{List_size: <RecFunction>, …}`` for the SMT translation env."""
    out: dict[str, Any] = {}
    for name, entries in _measures_by_aeon_name.items():
        fun = lookup_measure(name)
        if fun is not None:
            out[name] = fun
    return out


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
