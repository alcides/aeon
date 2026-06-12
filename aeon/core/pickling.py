"""Pickle support for the Rust core AST (``aeon_rs``).

The aeon_rs pyclasses are not dataclasses, so pickle/dill cannot derive
reducers for them — and the synthesis evaluation pool ships core ``Term``
trees through ``multiprocess`` queues. Register :mod:`copyreg` reducers that
rebuild each node from its ``__match_args__`` fields (passed back to the
constructor as keywords); singleton enums (``Kind``, ``Multiplicity``) are
restored by name so identity-based matching keeps working across processes.

Imported for its side effect from :mod:`aeon.core.terms` and
:mod:`aeon.core.types`.
"""

from __future__ import annotations

import copyreg

import aeon_rs


def _construct(cls, kwargs):
    return cls(**kwargs)


def _fields_reducer(cls, fields):
    def _reduce(obj):
        return _construct, (cls, {f: getattr(obj, f) for f in fields})

    return _reduce


def _singleton_reducer(obj):
    # ``Kind.BASE`` / ``Multiplicity.M0`` etc. are class attributes returning
    # the per-process singleton, so ``getattr(cls, name)`` restores identity.
    return getattr, (type(obj), obj.name)


def _empty_reducer(cls):
    def _reduce(_obj):
        return cls, ()

    return _reduce


# ``__match_args__`` is the constructor surface for almost every class; the
# exceptions are listed here explicitly.
_FIELD_OVERRIDES: dict[str, tuple[str, ...]] = {
    # __match_args__ omits multiplicity, which must survive a round trip.
    "AbstractionType": ("var_name", "var_type", "type", "loc", "multiplicity"),
}

_SINGLETON_ENUMS = {"Kind", "Multiplicity"}

# Field-less node classes (no __match_args__) that can appear inside an AST.
_EMPTY_NODES = {"LiquidHole"}


def _register() -> None:
    for cname in dir(aeon_rs):
        cls = getattr(aeon_rs, cname)
        if not isinstance(cls, type):
            continue
        if cname in _SINGLETON_ENUMS:
            copyreg.pickle(cls, _singleton_reducer)
            continue
        if cname in _EMPTY_NODES:
            copyreg.pickle(cls, _empty_reducer(cls))
            continue
        fields = _FIELD_OVERRIDES.get(cname) or getattr(cls, "__match_args__", None)
        if fields:
            copyreg.pickle(cls, _fields_reducer(cls, tuple(fields)))


_register()
