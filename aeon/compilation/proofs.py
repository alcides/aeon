"""Finish explicit theorem tactics during compilation and reject open proofs."""

from dataclasses import replace, fields, is_dataclass

from aeon.core.terms import Rec
from aeon.core.types import AbstractionType, RefinementPolymorphism, TypePolymorphism
from aeon.errors import AeonError
from aeon.synthesis.identification import get_holes, get_holes_info
from aeon.synthesis.tactics.explicit_synth import ExplicitTacticSynthesizer
from aeon.synthesis.tactics.holes import replace_hole
from aeon.synthesis.uis.api import SilentSynthesisUI
from aeon.typechecking.typeinfer import check_type, check_type_errors


class IncompleteTheoremError(AeonError):
    def __init__(self, name, loc, detail):
        self.name, self.loc, self.detail = name, loc, detail

    def __str__(self):
        return f"Theorem '{self.name}' is incomplete: {self.detail}"

    def position(self):
        return self.loc


def check_theorem_statements(program):
    from aeon.sugar.program import SHole, STerm
    from aeon.sugar.stypes import SType

    def has_hole(node):
        if isinstance(node, SHole):
            return True
        if isinstance(node, (list, tuple)):
            return any(has_hole(item) for item in node)
        return (
            isinstance(node, (STerm, SType))
            and is_dataclass(node)
            and any(has_hole(getattr(node, field.name)) for field in fields(node))
        )

    for definition in program.definitions:
        if definition.is_theorem and (has_hole(definition.type) or has_hole(definition.args)):
            raise IncompleteTheoremError(definition.name.name, definition.loc, "unresolved hole in theorem statement")


def complete_theorems(core, ctx, theorem_names, metadata, export_prefix=None):
    names = {f"{export_prefix}_{name}" if export_prefix else name for name in theorem_names}
    scripts = {
        hole.name: steps
        for entry in metadata.values()
        if isinstance(entry, dict)
        for hole, steps in entry.get("tactic_scripts", {}).items()
    }

    unfinished = set()

    def references(node):
        from aeon.core.terms import Var, Term
        from aeon.core.types import Type
        from aeon.core.liquid import LiquidTerm, LiquidVar, LiquidApp

        result = set()
        if isinstance(node, (Var, LiquidVar)):
            result.add(node.name)
        elif isinstance(node, LiquidApp):
            result.add(node.fun)
        if isinstance(node, (Term, Type, LiquidTerm)) and is_dataclass(node):
            for field in fields(node):
                value = getattr(node, field.name)
                if isinstance(value, (list, tuple)):
                    for item in value:
                        result.update(references(item))
                else:
                    result.update(references(value))
        return result

    def walk(node, local):
        if not isinstance(node, Rec):
            return node
        value = node.var_value
        dependencies = (references(value) | references(node.var_type)) & unfinished
        if node.var_name.name in names:
            if dependencies:
                raise IncompleteTheoremError(
                    node.var_name.name,
                    node.loc,
                    "depends on unfinished definition(s): " + ", ".join(sorted(n.name for n in dependencies)),
                )
            for hole in get_holes(value):
                steps = scripts.get(hole.name)
                if steps is None:
                    raise IncompleteTheoremError(node.var_name.name, node.loc, f"unresolved goal ?{hole.name}")
                info = get_holes_info(local, value, node.var_type, [], refined_types=True)
                expected, hole_ctx = info[hole]
                candidate = ExplicitTacticSynthesizer(tuple(steps)).synthesize(
                    hole_ctx,
                    expected,
                    lambda t: check_type(hole_ctx, t, expected),
                    lambda _: [],
                    node.var_name,
                    metadata,
                    ui=SilentSynthesisUI(),
                )
                if candidate is None:
                    raise IncompleteTheoremError(node.var_name.name, node.loc, "tactic script left an unsolved goal")
                value = replace_hole(value, hole, candidate)
            if get_holes(value):
                raise IncompleteTheoremError(node.var_name.name, node.loc, "unresolved proof goals")
        if get_holes(value) or dependencies:
            unfinished.add(node.var_name)
        body = walk(node.body, local.with_var(node.var_name, node.var_type))
        if node.var_name.name in names and not isinstance(
            node.var_type, (AbstractionType, TypePolymorphism, RefinementPolymorphism)
        ):
            # A constant theorem cannot use its own proposition as a premise.
            errors = list(check_type_errors(local, value, node.var_type))
            if errors:
                raise errors[0]
        return replace(node, var_value=value, body=body)

    return walk(core, ctx)
