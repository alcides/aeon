"""Compilation-local class and instance metadata used by elaboration."""

from __future__ import annotations

from dataclasses import dataclass, field, replace

from aeon.compilation.session import SessionMapping, current_session
from aeon.core.types import Kinding, Kind, constructor_kind
from aeon.errors import TypeClassError
from aeon.sugar.stypes import SAbstractionType, SRefinedType, SType, STypeConstructor, STypeVar, STypePolymorphism
from aeon.utils.name import Name


@dataclass(frozen=True)
class InstanceInfo:
    dict_name: Name
    foralls: tuple[Name, ...]
    num_constraints: int
    type_args: tuple[SType, ...] = field(default_factory=tuple)
    constraints: tuple[SType, ...] = field(default_factory=tuple)


@dataclass(frozen=True)
class ClassInfo:
    parameters: tuple[tuple[Name, Kinding], ...]
    # Each superclass has a checked dictionary projection, with explicit input.
    supers: tuple[tuple[Name, SType], ...]


@dataclass
class InstanceRegistry:
    instances: dict[str, tuple[InstanceInfo, ...]] = field(default_factory=dict)
    classes: dict[str, ClassInfo] = field(default_factory=dict)


_instances = SessionMapping(lambda: current_session().state(InstanceRegistry).instances)
_classes = SessionMapping(lambda: current_session().state(InstanceRegistry).classes)


def _shape(t: SType, variables: set[Name], scope: int) -> tuple:
    match t:
        case SRefinedType(_, inner, _):
            return _shape(inner, variables, scope)
        case STypeVar(n) if n in variables:
            return ("var", scope, n)
        case STypeVar(n):
            return ("type", n.name, ())
        case STypeConstructor(n, args):
            shape: tuple = ("var", scope, n) if n in variables else ("type", n.name, ())
            for argument in args:
                shape = ("type", "apply", (shape, _shape(argument, variables, scope)))
            return shape
        case SAbstractionType(_, domain, codomain):
            return ("type", "->", (_shape(domain, variables, scope), _shape(codomain, variables, scope)))
        case _:
            return ("rigid", str(t))


def _overlap(left: InstanceInfo, right: InstanceInfo) -> bool:
    """First-order unification of *all* head arguments, with disjoint variables.

    Repeated variables share their substitution, and the occurs check rules out
    infinite types. Constraints do not make overlapping heads coherent.
    """
    subst: dict[tuple, tuple] = {}

    def resolve(t: tuple) -> tuple:
        while t in subst:
            t = subst[t]
        return t

    def occurs(v: tuple, t: tuple) -> bool:
        t = resolve(t)
        return v == t or (t[0] == "type" and any(occurs(v, a) for a in t[2]))

    def unify(a: tuple, b: tuple) -> bool:
        a, b = resolve(a), resolve(b)
        if a == b:
            return True
        if a[0] == "var":
            if occurs(a, b):
                return False
            subst[a] = b
            return True
        if b[0] == "var":
            return unify(b, a)
        if a[0] == b[0] == "type" and a[1] == b[1] and len(a[2]) == len(b[2]):
            return all(unify(x, y) for x, y in zip(a[2], b[2]))
        return False

    return len(left.type_args) == len(right.type_args) and all(
        unify(_shape(a, set(left.foralls), 0), _shape(b, set(right.foralls), 1))
        for a, b in zip(left.type_args, right.type_args)
    )


def register_instance(class_name: str, info: InstanceInfo) -> None:
    previous = _instances.get(class_name, ())
    for other in previous:
        if _overlap(other, info):
            raise TypeClassError(
                f"Overlapping instances for '{class_name}': '{other.dict_name.name}' and '{info.dict_name.name}'"
            )
    _instances[class_name] = (*previous, info)


def lookup_instances(class_name: str) -> tuple[InstanceInfo, ...]:
    return _instances.get(class_name, ())


def register_class(name: str, info: ClassInfo) -> None:
    if name in _classes:
        raise TypeClassError(f"Duplicate class '{name}'")
    _classes[name] = info


def lookup_class(name: str) -> ClassInfo | None:
    return _classes.get(name)


def clear_instance_registry() -> None:
    _instances.clear()
    _classes.clear()


def qualify_instance_providers(names: dict[str, Name]) -> None:
    """Keep elaboration's implicit references aligned with module renaming."""
    for class_name, instances in list(_instances.items()):
        _instances[class_name] = tuple(
            replace(info, dict_name=names.get(info.dict_name.name, info.dict_name)) for info in instances
        )
    for class_name, info in list(_classes.items()):
        _classes[class_name] = replace(info, supers=tuple((names.get(name.name, name), ty) for name, ty in info.supers))


def infer_type_variable_kinds(types: list[SType]) -> dict[Name, Kinding]:
    """Infer implicit parameter kinds from class signatures and constructor uses."""
    inferred: dict[Name, Kinding] = {}

    def visit(ty: SType) -> None:
        match ty:
            case STypeConstructor(name, arguments):
                cls = lookup_class(name.name)
                if cls is not None:
                    for (_, kind), argument in zip(cls.parameters, arguments):
                        if isinstance(argument, STypeVar):
                            inferred[argument.name] = kind
                elif name.name[:1].islower():
                    inferred.setdefault(name, constructor_kind([Kind.BASE] * len(arguments)))
                for argument in arguments:
                    visit(argument)
            case SAbstractionType(_, domain, codomain):
                visit(domain)
                visit(codomain)
            case SRefinedType(_, inner, _) | STypePolymorphism(_, _, inner):
                visit(inner)

    for ty in types:
        visit(ty)
    return inferred
