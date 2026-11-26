"""Non-fatal diagnostics for impossible parameter refinements."""

from dataclasses import dataclass, fields

from z3 import FreshBool, Implies, Solver, unsat
from z3.z3types import Z3Exception

from aeon.compilation.session import current_session
from aeon.core.liquid import LiquidLiteralBool, LiquidVar
from aeon.core.substitutions import substitution_in_liquid
from aeon.core.terms import Term
from aeon.core.types import (
    Type,
    AbstractionType,
    RefinedType,
    RefinementPolymorphism,
    TypePolymorphism,
)
from aeon.core.types import TypeConstructor, TypeVar
from aeon.utils.location import Location, FileLocation
from aeon.verification.decidability import _location_in_file
from aeon.verification.smt import make_variable, translate_liq
from aeon.verification.sub import lower_constraint_type


@dataclass(frozen=True)
class FalseParameterWarning:
    location: Location
    message: str
    construct: str = "false parameter refinement"
    code: str = "false-parameter-refinement"
    parameters: tuple[str, ...] = ()
    related: tuple[tuple[Location, str], ...] = ()


def collect_false_parameter_warnings(term, *, source_path=None):
    warnings = []
    seen = set()

    def emit(warning):
        key = (warning.code, str(warning.location), warning.parameters)
        if _location_in_file(warning.location, source_path) and key not in seen:
            seen.add(key)
            warnings.append(warning)

    def parameter_location(param, owner_loc):
        # Lowering may synthesise the type location but preserve the predicate.
        if isinstance(param, RefinedType) and isinstance(param.refinement.loc, FileLocation):
            return param.refinement.loc
        return param.loc if isinstance(param.loc, FileLocation) else owner_loc

    def check_parameters(params, owner_loc):
        if not any(_location_in_file(parameter_location(param, owner_loc), source_path) for _, param in params):
            return
        # Literal-false parameters retain their existing diagnostic. Avoid a
        # second warning for the same impossible signature.
        literal_false = False
        for name, param in params:
            if isinstance(param, RefinedType) and param.refinement == LiquidLiteralBool(False):
                literal_false = True
                loc = parameter_location(param, owner_loc)
                emit(
                    FalseParameterWarning(
                        loc,
                        f"Parameter '{name.name}' has refinement false: no value can satisfy it. "
                        "The function body is checked under an impossible assumption.",
                        parameters=(name.name,),
                    )
                )
        if literal_false or not any(isinstance(param, RefinedType) for _, param in params):
            return

        # A separate bounded solver keeps this advisory query out of the
        # program's proof evidence and does not change typechecking acceptance.
        solver = Solver()
        timeout = current_session().options.smt_timeout_ms
        solver.set(timeout=min(timeout, 200) if timeout > 0 else 200)
        env = {}
        assumptions = []
        for name, param in params:
            base = param.type if isinstance(param, RefinedType) else param
            if not isinstance(base, (TypeConstructor, TypeVar)):
                continue
            try:
                env[str(name)] = make_variable(str(name), lower_constraint_type(base))
                if not isinstance(param, RefinedType) or param.refinement == LiquidLiteralBool(True):
                    continue
                predicate = substitution_in_liquid(param.refinement, LiquidVar(name), param.name)
                formula = translate_liq(predicate, env)
                label = FreshBool("parameter-assumption")
                solver.add(Implies(label, formula))
                assumptions.append((label, name, param))
            except (
                Z3Exception,
                KeyError,
                TypeError,
                ValueError,
                AssertionError,
                ZeroDivisionError,
            ):
                # Unsupported predicates cannot establish a contradiction.
                # Independently translatable assumptions remain useful.
                continue
        if not assumptions or solver.check(*(label for label, _, _ in assumptions)) != unsat:
            return
        core = {label.get_id() for label in solver.unsat_core()}
        conflicting = [(name, param) for label, name, param in assumptions if label.get_id() in core]
        if not conflicting:
            return
        names = tuple(name.name for name, _ in conflicting)
        locations = tuple(
            (
                parameter_location(param, owner_loc),
                f"Assumption '{name.name}'",
            )
            for name, param in conflicting
        )
        if len(names) == 1:
            message = f"Parameter '{names[0]}' has an unsatisfiable refinement: no value can satisfy it. "
        else:
            message = f"Parameter hypotheses {', '.join(repr(name) for name in names)} are contradictory: "
            message += "no arguments can satisfy them together. "
        emit(
            FalseParameterWarning(
                locations[-1][0],
                message + "The function body is checked under impossible assumptions; verification is vacuous.",
                construct="contradictory parameter hypotheses",
                code="contradictory-parameter-hypotheses",
                parameters=names,
                related=locations,
            )
        )

    def visit(ty, owner_loc):
        if isinstance(ty, AbstractionType):
            params = []
            while isinstance(ty, (AbstractionType, TypePolymorphism, RefinementPolymorphism)):
                if isinstance(ty, AbstractionType):
                    visit(ty.var_type, owner_loc)
                    params.append((ty.var_name, ty.var_type))
                    ty = ty.type
                else:
                    ty = ty.body
            check_parameters(params, owner_loc)
        elif isinstance(ty, (TypePolymorphism, RefinementPolymorphism)):
            visit(ty.body, owner_loc)

    def walk(node, loc):
        if isinstance(node.loc, FileLocation):
            loc = node.loc
        for field in fields(node):
            value = getattr(node, field.name)
            if isinstance(value, Type):
                visit(value, loc)
            elif isinstance(value, Term):
                walk(value, loc)

    walk(term, term.loc)
    return warnings
