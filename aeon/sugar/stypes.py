"""Surface-level type representation. Re-exports the Rust core (aeon_rs)
plus the Python-side `get_type_vars` helper and the `builtin_types` list.
"""

from __future__ import annotations

from aeon_rs import SAbstractionType as SAbstractionType
from aeon_rs import SRefinedType as SRefinedType
from aeon_rs import SRefinementPolymorphism as SRefinementPolymorphism
from aeon_rs import SType as SType
from aeon_rs import STypeConstructor as STypeConstructor
from aeon_rs import STypePolymorphism as STypePolymorphism
from aeon_rs import STypeVar as STypeVar

from functools import reduce

builtin_types = ["Top", "Bool", "Int", "Float", "String", "Unit", "Set", "Tensor", "GpuConfig"]


def get_type_vars(ty: SType) -> set[STypeVar]:
    match ty:
        case STypeVar(name):
            return {ty}
        case SAbstractionType(_, vtype, rtype):
            return get_type_vars(vtype).union(get_type_vars(rtype))
        case SRefinedType(_, rty, _):
            return get_type_vars(rty)
        case STypePolymorphism(name, _, body):
            return {t1 for t1 in get_type_vars(body) if t1.name != name}
        case SRefinementPolymorphism(name, _, body):
            return get_type_vars(body)
        case STypeConstructor(name, args):
            return reduce(lambda acc, v: acc.union(get_type_vars(v)), args, set())
        case _:
            assert False, f"Unknown type ({ty}) ({type(ty)})"
