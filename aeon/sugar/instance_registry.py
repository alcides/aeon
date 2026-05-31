"""Registry of typeclass instances for method resolution.

Populated during ``expand_typeclasses`` (desugar) and consumed during
elaboration to fill in instance-implicit dictionary arguments at method call
sites. Keyed by ``(class_name, head_type_name)`` where ``head_type_name`` is the
outermost type constructor of the class's (first) type argument — e.g. the
instance ``Eq (List a)`` is keyed ``("Eq", "List")``.

Cleared once per top-level compilation by the driver.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from aeon.sugar.stypes import SType
from aeon.utils.name import Name


@dataclass(frozen=True)
class InstanceInfo:
    # Name of the generated dictionary definition (e.g. ``__inst_Eq_Int``).
    dict_name: Name
    # Names of the ``forall`` type binders of the dictionary definition, in
    # order. Referencing the dict requires one type application per binder.
    foralls: tuple[Name, ...]
    # Number of leading instance-implicit (constraint) arguments the dict takes,
    # e.g. ``instance [Eq a] : Eq (List a)`` has one.
    num_constraints: int
    # The instance's declared type-argument pattern (e.g. ``(Box a,)`` for
    # ``instance [Eq a] : Eq (Box a)``). Used to unify against a requested type
    # and recover the ``forall`` bindings during resolution.
    type_args: tuple[SType, ...] = field(default_factory=tuple)
    # The constraint class-types (e.g. ``(Eq a,)``), in the same order as the
    # dict's instance-implicit parameters. Resolved recursively, after applying
    # the unifying substitution, to nested dictionaries.
    constraints: tuple[SType, ...] = field(default_factory=tuple)


# (class_name, head_type_name) -> InstanceInfo
_instances: dict[tuple[str, str], InstanceInfo] = {}


def register_instance(class_name: str, head: str, info: InstanceInfo) -> None:
    _instances[(class_name, head)] = info


def lookup_instance(class_name: str, head: str) -> InstanceInfo | None:
    return _instances.get((class_name, head))


def clear_instance_registry() -> None:
    _instances.clear()
