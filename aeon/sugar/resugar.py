"""Recover surface matches from applications of generated inductive eliminators.

Recognition uses the bound eliminator definition, not an ``_rec`` suffix alone.
The call may come from source, synthesis, or match lowering. This pass is only
for display; ordinary Core-to-sugar lifting remains structure preserving.
"""

from dataclasses import dataclass, field, fields, is_dataclass, replace

from aeon.compilation.session import current_session
from aeon.core import terms as core
from aeon.core import types as ctypes
from aeon.sugar.program import (
    SAbstraction,
    SApplication,
    SLiteral,
    SMatch,
    SMatchBranch,
    SRec,
    SRefinementAbstraction,
    SRefinementApplication,
    STerm,
    STypeAbstraction,
    STypeApplication,
    SVar,
)
from aeon.sugar.stypes import (
    SType,
    SAbstractionType,
    SRefinedType,
    STypeConstructor,
    STypePolymorphism,
    SRefinementPolymorphism,
)
from aeon.sugar.substitutions import substitute_svartype_in_stype, substitution_sterm_in_stype
from aeon.utils.name import Name, fresh_counter


@dataclass(frozen=True)
class Recursor:
    qualifier: str
    constructors: tuple[tuple[str, int], ...]
    signature: SType


def _recursor(binding) -> Recursor | None:
    """Verify the compiler-generated dispatcher and recover its pattern schema.

    Derive this from either a Core or sugar binding so cached modules and whole
    lifted programs work without relying on ambient constructor registration.
    """
    if not binding.var_name.name.endswith("_rec"):
        return None
    ty = binding.var_type
    while isinstance(
        ty, (ctypes.TypePolymorphism, ctypes.RefinementPolymorphism, STypePolymorphism, SRefinementPolymorphism)
    ):
        ty = ty.body
    if not isinstance(ty, (ctypes.AbstractionType, SAbstractionType)):
        return None
    actual = ty.var_type
    if isinstance(actual, (ctypes.RefinedType, SRefinedType)):
        actual = actual.type
    if not isinstance(actual, (ctypes.TypeConstructor, STypeConstructor)):
        return None
    value = binding.var_value
    while isinstance(
        value, (core.TypeAbstraction, core.RefinementAbstraction, STypeAbstraction, SRefinementAbstraction)
    ):
        value = value.body
    if not isinstance(value, (core.Abstraction, SAbstraction)):
        return None
    scrutinee = value.var_name.name
    value = value.body
    ty = ty.type
    constructors = []
    handlers = []
    while isinstance(value, (core.Abstraction, SAbstraction)) and isinstance(
        ty, (ctypes.AbstractionType, SAbstractionType)
    ):
        label = value.var_name.name
        if not label.startswith("case_"):
            return None
        arity = 0
        handler_type = ty.var_type
        while isinstance(handler_type, (ctypes.AbstractionType, SAbstractionType)):
            arity += 1
            handler_type = handler_type.type
        constructors.append((label.removeprefix("case_"), arity))
        handlers.append(label)
        value, ty = value.body, ty.type
    if not constructors or not isinstance(value, (core.Application, SApplication)):
        return None
    native = value.fun
    while isinstance(native, (core.TypeApplication, STypeApplication)):
        native = native.body
    if not isinstance(native, (core.Var, SVar)) or native.name != Name("native", 0):
        return None
    if not isinstance(value.arg, (core.Literal, SLiteral)):
        return None
    expected = "(_ for _ in ()).throw(Exception('Invalid constructor'))"
    for (constructor, arity), handler in reversed(list(zip(constructors, handlers))):
        call = handler + "".join(f"({scrutinee}[{i + 1}])" for i in range(arity))
        expected = f"({call} if {scrutinee}[0] == '{actual.name.name}_{constructor}' else {expected})"
    if value.arg.value != expected:
        return None
    from aeon.sugar.lifting import lift_type

    signature = lift_type(binding.var_type) if isinstance(binding, core.Rec) else binding.var_type
    return Recursor(actual.name.name, tuple(constructors), signature)


@dataclass
class _RecursorPrinting:
    schemas: dict[Name, Recursor] = field(default_factory=dict)


def register_recursors(program: core.Term) -> None:
    """Record bound eliminators once after linking, including cached modules.

    Standalone synthesized expressions can then use the same schemas as whole
    programs, without rescanning all dependencies for every displayed candidate.
    """
    schemas = current_session().state(_RecursorPrinting).schemas
    binding = program
    while isinstance(binding, (core.Let, core.Rec)):
        if isinstance(binding, core.Rec) and (schema := _recursor(binding)) is not None:
            schemas[binding.var_name] = schema
        binding = binding.body


def restore_matches(term: STerm) -> STerm:
    recursors = dict(current_session().state(_RecursorPrinting).schemas)
    used: set[str] = set()

    def inventory(node):
        if isinstance(node, Name):
            used.add(node.name)
        elif is_dataclass(node):
            if isinstance(node, SRec) and (schema := _recursor(node)) is not None:
                recursors[node.var_name] = schema
            for descriptor in fields(node):
                inventory(getattr(node, descriptor.name))
        elif isinstance(node, (list, tuple)):
            for child in node:
                inventory(child)

    inventory(term)

    def fresh(label: str) -> Name:
        spelling = label
        while spelling in used:
            spelling = f"{label}_{fresh_counter.fresh()}"
        used.add(spelling)
        return Name(spelling, fresh_counter.fresh())

    def children(node):
        if isinstance(node, STerm):
            return visit(node)
        if isinstance(node, SMatchBranch):
            return replace(node, body=visit(node.body))
        if isinstance(node, list):
            return [children(child) for child in node]
        if isinstance(node, tuple):
            return tuple(children(child) for child in node)
        return node

    def visit(node: STerm) -> STerm:
        if isinstance(node, SApplication):
            head: STerm = node
            arguments = []
            while isinstance(head, SApplication):
                arguments.append(head.arg)
                head = head.fun
            arguments.reverse()
            instantiations = []
            while isinstance(head, (STypeApplication, SRefinementApplication)):
                instantiations.append(head)
                head = head.body
            schema = recursors.get(head.name) if isinstance(head, SVar) else None
            if schema is not None and len(arguments) >= len(schema.constructors) + 1:
                count = len(schema.constructors) + 1
                supplied = [visit(argument) for argument in arguments[:count]]
                bindings = []
                # Eta-expanding a computed handler would defer its evaluation
                # until its branch is selected. Evaluate all supplied arguments
                # in their original order first if any handler needs that.
                if any(
                    arity and not isinstance(handler, (SAbstraction, SVar))
                    for (_, arity), handler in zip(schema.constructors, supplied[1:])
                ):
                    signature = schema.signature
                    for instantiation in reversed(instantiations):
                        if isinstance(instantiation, STypeApplication) and isinstance(signature, STypePolymorphism):
                            signature = substitute_svartype_in_stype(signature.body, instantiation.type, signature.name)
                        elif isinstance(instantiation, SRefinementApplication) and isinstance(
                            signature, SRefinementPolymorphism
                        ):
                            signature = substitution_sterm_in_stype(
                                signature.body, instantiation.refinement, signature.name
                            )
                    for index, argument in enumerate(supplied):
                        if not isinstance(signature, SAbstractionType):
                            return node
                        name = fresh("match_value" if index == 0 else "match_handler")
                        bindings.append((name, signature.var_type, argument, signature.multiplicity))
                        supplied[index] = SVar(name)
                        signature = substitution_sterm_in_stype(signature.type, supplied[index], signature.var_name)
                branches = []
                for (constructor, arity), handler in zip(schema.constructors, supplied[1:]):
                    binders = []
                    body = handler
                    for _ in range(arity):
                        if isinstance(body, SAbstraction):
                            binders.append(body.var_name)
                            body = body.body
                        else:
                            name = fresh("field")
                            binders.append(name)
                            body = SApplication(body, SVar(name))
                    branches.append(SMatchBranch(Name(constructor, 0), binders, body, qualifier=schema.qualifier))
                result: STerm = SMatch(supplied[0], branches, loc=node.loc)
                for argument in arguments[count:]:
                    result = SApplication(result, visit(argument), loc=node.loc)
                for index in range(len(bindings) - 1, -1, -1):
                    name, ty, value, multiplicity = bindings[index]
                    result = SRec(name, ty, value, result, multiplicity=multiplicity)
                return result
        if not is_dataclass(node):
            return node
        return replace(
            node, **{descriptor.name: children(getattr(node, descriptor.name)) for descriptor in fields(node)}
        )

    return visit(term)
