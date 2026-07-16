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

from aeon.core.multiplicity import Multiplicity, MOmega
from aeon.core.types import Kind

from typing import TYPE_CHECKING


from aeon.utils.location import Location, SynthesizedLocation
from aeon.utils.name import Name

if TYPE_CHECKING:
    from aeon.sugar.program import STerm


class SType(ABC):
    "Surface-level Type Representation"

    loc: Location


@dataclass(unsafe_hash=True)
class STypeVar(SType):
    name: Name
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"'{self.name}"


@dataclass(unsafe_hash=True)
class SRefinedType(SType):
    name: Name
    type: SType
    refinement: "STerm"
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"{{{self.name} : {self.type} | {self.refinement} }}"


@dataclass(unsafe_hash=True)
class SAbstractionType(SType):
    var_name: Name
    var_type: SType
    type: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))
    multiplicity: Multiplicity = MOmega
    # When True this binder is an *instance-implicit* parameter (Lean ``[C a]``
    # / typeclass-method dictionary). Such arguments are not written at call
    # sites; elaboration inserts an instance hole and resolves it from the
    # instance database. Plain binders keep the default ``False``.
    is_instance: bool = False

    def __str__(self):
        prefix = "" if self.multiplicity is MOmega else f"{self.multiplicity} "
        if self.is_instance:
            return f"[{self.var_name} : {self.var_type}] -> {self.type}"
        return f"({prefix}{self.var_name} : {self.var_type}) -> {self.type}"


@dataclass(unsafe_hash=True)
class STypePolymorphism(SType):
    name: Name
    kind: Kind
    body: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"∀{self.name}:{self.kind}. {self.body}"


@dataclass(unsafe_hash=True)
class SRefinementPolymorphism(SType):
    name: Name
    sort: SType
    body: SType
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        return f"∀<{self.name}:{self.sort}>. {self.body}"


@dataclass
class STypeConstructor(SType):
    name: Name
    args: list[SType] = field(default_factory=list)
    loc: Location = field(default_factory=lambda: SynthesizedLocation("default"))

    def __str__(self):
        args = ", ".join(str(a) for a in self.args)
        return f"{self.name} {args}"

    def __hash__(self):
        return hash(self.name) + sum(hash(c) for c in self.args)


builtin_types = ["Top", "Bool", "Int", "Float", "String", "Unit", "Set", "Tensor"]


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
