"""Shared whole-program verification conditions for joint SMT/SyGuS synthesis.

Unknown expressions become first-order functions of their lexical inputs.
Global unknowns are shared solver symbols, never independent universal inputs.
The ordinary compiler supplies the obligations; no refinement is assumed about
an unknown implementation before those obligations have been discharged.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from aeon.core.bind import populate_mutual_companions
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar, liquid_free_vars
from aeon.core.substitutions import substitution, liquefy, substitution_in_liquid
from aeon.core.terms import Abstraction, Application, Let, Literal, Rec, Term, Var
from aeon.core.types import AbstractionType, RefinedType, Type, TypeConstructor, t_bool, t_float, t_int
from aeon.decorators.api import Metadata
from aeon.synthesis.api import SynthesisNotSuccessful
from aeon.synthesis.fitness_eval import without_main_placeholder
from aeon.synthesis.joint import HoleSpec, JointSynthesizer
from aeon.typechecking.context import TypingContext, ReflectedBinder
from aeon.typechecking.entailment import entailment_context
from aeon.typechecking.typeinfer import check
from aeon.utils.name import Name, fresh_counter
from aeon.verification.helpers import simplify_expr
from aeon.verification.smt import flatten

BASES = (t_int, t_bool, t_float)
OPERATORS = frozenset({"+", "-", "*", "/", "%", "<", "<=", ">", ">=", "==", "!=", "&&", "||", "!", "-->", "ite"})


def base_type(ty: Type) -> TypeConstructor:
    base = ty.type if isinstance(ty, RefinedType) else ty
    if base not in BASES:
        raise SynthesisNotSuccessful(f"Joint solver cannot translate type {ty}; expected Int, Bool or Float")
    assert isinstance(base, TypeConstructor)
    return base


@dataclass(frozen=True)
class SolverHole:
    name: Name
    symbol: Name
    params: tuple[tuple[Name, TypeConstructor], ...]
    abstractions: tuple[Name, ...]
    base: TypeConstructor

    @property
    def dummy(self) -> bool:
        return not self.params

    def wrap(self, body: Term) -> Term:
        for name in reversed(self.abstractions):
            body = Abstraction(name, body)
        return body


@dataclass(frozen=True)
class SolverClause:
    variables: tuple[tuple[Name, TypeConstructor], ...]
    premise: LiquidTerm
    conclusion: LiquidTerm


@dataclass(frozen=True)
class SolverProblem:
    holes: tuple[SolverHole, ...]
    clauses: tuple[SolverClause, ...]


class ConstraintSynthesizer(JointSynthesizer):
    """Marker for backends needing the compiler's shared logical obligations."""


# Only strengthen property return contracts; preserve domains and multiplicities.
def _true_return(ty: Type) -> Type:
    if isinstance(ty, AbstractionType):
        return replace(ty, type=_true_return(ty.type))
    if base_type(ty) != t_bool:
        raise SynthesisNotSuccessful("Joint solver properties must return Bool")
    name = Name("property_result", fresh_counter.fresh())
    return RefinedType(name, t_bool, LiquidVar(name))


def _strengthen(program: Term, properties: set[Name]) -> Term:
    if isinstance(program, Rec):
        return replace(
            program,
            body=_strengthen(program.body, properties),
            var_type=_true_return(program.var_type) if program.var_name in properties else program.var_type,
        )
    if isinstance(program, Let):
        return replace(program, body=_strengthen(program.body, properties))
    return program


def _check_liquid(term: LiquidTerm, symbols: set[Name]) -> None:
    if isinstance(term, LiquidApp):
        if term.fun not in symbols and term.fun.name not in OPERATORS:
            raise SynthesisNotSuccessful(f"Joint solver cannot translate function {term.fun.name}")
        for arg in term.args:
            _check_liquid(arg, symbols)
    elif not isinstance(term, (LiquidVar, LiquidLiteralBool)):
        from aeon.core.liquid import LiquidLiteralInt, LiquidLiteralFloat

        if not isinstance(term, (LiquidLiteralInt, LiquidLiteralFloat)):
            raise SynthesisNotSuccessful(f"Joint solver cannot translate predicate {term}")


def build_solver_problem(
    ctx: TypingContext,
    program: Term,
    holes: tuple[HoleSpec, ...],
    metadata: Metadata,
) -> SolverProblem:
    """Preserve all hole contracts, surrounding refinements and example relations."""
    program = without_main_placeholder(program)
    globals_ = {entry.name for entry in ctx.entries if hasattr(entry, "name")}
    schemas = []
    symbolic = program
    symbolic_ctx = ctx
    for hole in holes:
        local = tuple(
            (n, base_type(ty))
            for n, ty in hole.ctx.concrete_vars()
            if n not in globals_ and (ty.type if isinstance(ty, RefinedType) else ty) in BASES
        )
        params = list(local)
        abstractions = []
        ty = hole.type
        while isinstance(ty, AbstractionType):
            params.append((ty.var_name, base_type(ty.var_type)))
            abstractions.append(ty.var_name)
            ty = ty.type
        base = base_type(ty)
        symbol = Name("joint_" + hole.name.name, fresh_counter.fresh())
        schema = SolverHole(hole.name, symbol, tuple(params), tuple(abstractions), base)
        schemas.append(schema)
        arguments: list[Term] = [Var(n) for n, _ in params]
        if not arguments:
            arguments = [Literal(0, t_int)]
        signature: Type = base
        declarations = params or [(Name("unused", fresh_counter.fresh()), t_int)]
        for name, param_type in reversed(declarations):
            signature = AbstractionType(name, param_type, signature)
        symbolic_ctx = symbolic_ctx.with_var(symbol, signature)
        value: Term = Var(symbol)
        for arg in arguments:
            value = Application(value, arg)
        symbolic = substitution(symbolic, schema.wrap(value), hole.name)

    properties = {name for name, entry in metadata.items() if isinstance(entry, dict) and "property" in entry}
    examples = {
        ex.function for entry in metadata.values() if isinstance(entry, dict) for ex in entry.get("examples", [])
    }
    symbolic = populate_mutual_companions(_strengthen(symbolic, properties | examples))
    from aeon.verification.vcs import Conjunction, Constraint, LiquidConstraint, ReflectedFunctionDeclaration

    constraints: Constraint = LiquidConstraint(LiquidLiteralBool(True))
    prefix_ctx = symbolic_ctx
    reflections: list[ReflectedBinder] = []
    current = symbolic
    try:
        while isinstance(current, (Let, Rec)):
            if not isinstance(current, Rec):
                raise SynthesisNotSuccessful("Joint solver requires typed top-level definitions")
            name, declared, value = current.var_name, current.var_type, current.var_value
            body = value
            actual_params = []
            while isinstance(body, Abstraction):
                actual_params.append(body.var_name)
                body = body.body
            logical = liquefy(body)
            if name in properties | examples:
                if logical is None:
                    raise SynthesisNotSuccessful("Joint solver cannot translate a native property/example")
                _check_liquid(logical, {h.symbol for h in schemas} | {r.name for r in reflections})
            obligation = entailment_context(prefix_ctx, check(prefix_ctx, value, declared))
            for reflection in reversed(reflections):
                obligation = ReflectedFunctionDeclaration(
                    reflection.name, reflection.type, reflection.params, reflection.body, obligation
                )
            constraints = Conjunction(constraints, obligation)
            if isinstance(declared, AbstractionType) and logical is not None:
                formal = []
                ret: Type = declared
                while isinstance(ret, AbstractionType):
                    formal.append(ret.var_name)
                    ret = ret.type
                if len(formal) == len(actual_params):
                    for old, new in zip(actual_params, formal):
                        logical = substitution_in_liquid(logical, LiquidVar(new), old)
                    reflection = ReflectedBinder(name, declared, tuple(formal), logical)
                    reflections.append(reflection)
                    prefix_ctx = prefix_ctx.with_var(name, declared)
                else:
                    prefix_ctx = prefix_ctx.with_var(name, declared)
            elif logical is not None and (declared.type if isinstance(declared, RefinedType) else declared) in BASES:
                binder = Name("bound_value", fresh_counter.fresh())
                equality = LiquidApp(Name("==", 0), [LiquidVar(binder), logical])
                if isinstance(declared, RefinedType):
                    predicate = substitution_in_liquid(declared.refinement, LiquidVar(binder), declared.name)
                    equality = LiquidApp(Name("&&", 0), [equality, predicate])
                prefix_ctx = prefix_ctx.with_var(name, RefinedType(binder, base_type(declared), equality))
            else:
                prefix_ctx = prefix_ctx.with_var(name, declared)
            current = current.body

        # A hole's own contract must hold over its declared scope, including
        # earlier globals with weak refinements. Do not specialize its function
        # to one chosen global value: the final Aeon validator retains that scope.
        for hole, schema in zip(holes, schemas):
            local_ctx = hole.ctx
            for generated in schemas:
                local_ctx = local_ctx.with_var(generated.symbol, symbolic_ctx.type_of(generated.symbol))
            value = Var(schema.symbol)
            inputs: list[Term] = [Var(n) for n, _ in schema.params]
            for arg in inputs or [Literal(0, t_int)]:
                value = Application(value, arg)
            obligation = entailment_context(local_ctx, check(local_ctx, schema.wrap(value), hole.type))
            for reflection in reversed(reflections):
                obligation = ReflectedFunctionDeclaration(
                    reflection.name, reflection.type, reflection.params, reflection.body, obligation
                )
            constraints = Conjunction(constraints, obligation)
        canonical = list(flatten(constraints))
    except SynthesisNotSuccessful:
        raise
    except Exception as exc:
        raise SynthesisNotSuccessful(f"Joint solver cannot construct verification conditions: {exc}") from exc
    symbols = {schema.symbol for schema in schemas}
    clauses = []
    for clause in canonical:
        conclusion = simplify_expr(clause.conclusion)
        if conclusion == LiquidLiteralBool(True):
            continue
        premise = simplify_expr(clause.premise)
        _check_liquid(premise, symbols)
        _check_liquid(conclusion, symbols)
        free = {n for expression in (premise, conclusion) for n in liquid_free_vars(expression)}
        variables = tuple(
            (n, base_type(clause.variables[str(n)])) for n in sorted(free, key=str) if str(n) in clause.variables
        )
        clauses.append(SolverClause(variables, premise, conclusion))
    return SolverProblem(tuple(schemas), tuple(clauses))
