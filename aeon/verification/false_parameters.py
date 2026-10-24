"""Non-fatal diagnostics for parameter refinements reduced to false."""

from dataclasses import dataclass, fields

from aeon.core.liquid import LiquidLiteralBool
from aeon.core.terms import Term
from aeon.core.types import Type, AbstractionType, RefinedType, RefinementPolymorphism, TypePolymorphism
from aeon.utils.location import Location
from aeon.verification.decidability import _location_in_file


@dataclass(frozen=True)
class FalseParameterWarning:
    location: Location
    message: str
    construct: str = "false parameter refinement"


def collect_false_parameter_warnings(term, *, source_path=None):
    warnings = []
    seen = set()

    def visit(ty, owner_loc):
        if isinstance(ty, AbstractionType):
            param = ty.var_type
            if isinstance(param, RefinedType) and param.refinement == LiquidLiteralBool(False):
                loc = param.loc if _location_in_file(param.loc, source_path) else owner_loc
                key = (str(loc), ty.var_name.name)
                if _location_in_file(loc, source_path) and key not in seen:
                    seen.add(key)
                    warnings.append(
                        FalseParameterWarning(
                            loc,
                            f"Parameter '{ty.var_name.name}' has refinement false: no value can satisfy it. "
                            "The function body is checked under an impossible assumption.",
                        )
                    )
            visit(param, owner_loc)
            visit(ty.type, owner_loc)
        elif isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            visit(ty.body, owner_loc)

    def walk(node, loc):
        if _location_in_file(node.loc, source_path):
            loc = node.loc
        for field in fields(node):
            value = getattr(node, field.name)
            if isinstance(value, Type):
                visit(value, loc)
            elif isinstance(value, Term):
                walk(value, loc)

    walk(term, term.loc)
    return warnings
