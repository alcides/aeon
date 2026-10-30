"""APPFO/APPHO checking and strengthening of unfinished application spines."""

from __future__ import annotations

from dataclasses import dataclass, field
from aeon.utils.name import Name

from aeon.core.liquid import LiquidVar
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.substitutions import substitution_in_liquid, substitution_in_type
from aeon.core.terms import Abstraction, Literal, Term, Var
from aeon.core.types import AbstractionType, RefinedType, Type, TypeConstructor, TypeVar, extract_parts
from aeon.synthesis.modules.synquid.constraints import ConstraintState, fresh_name
from aeon.synthesis.modules.synquid.solver import Status
from aeon.typechecking.typeinfer import check, synth
from aeon.verification.horn import split
from aeon.verification.sub import sub
from aeon.verification.vcs import variables_free_in


def match_result(pattern: Type, goal: Type, variables: set[Name]) -> dict[Name, Type] | None:
    """Goal-anchored shape discovery, retaining refinements at type variables."""
    p = pattern.type if isinstance(pattern, RefinedType) else pattern
    g = goal.type if isinstance(goal, RefinedType) else goal
    if isinstance(p, TypeVar) and p.name in variables:
        return {p.name: goal}
    if isinstance(p, AbstractionType) and isinstance(g, AbstractionType):
        left = match_result(p.var_type, g.var_type, variables)
        right = match_result(p.type, g.type, variables)
        if left is None or right is None:
            return None
        for n, ty in right.items():
            if n in left and erase(left[n]) != erase(ty):
                return None
            left[n] = merge_requirements(left[n], ty) if n in left else ty
        return left
    if isinstance(p, TypeConstructor) and isinstance(g, TypeConstructor):
        if p.name != g.name or len(p.args) != len(g.args):
            return None
        found: dict[Name, Type] = {}
        for a, b in zip(p.args, g.args):
            part = match_result(a, b, variables)
            if part is None:
                return None
            for name, ty in part.items():
                if name in found and erase(found[name]) != erase(ty):
                    return None
                found[name] = merge_requirements(found[name], ty) if name in found else ty
        return found
    return {} if p == g else None


def merge_requirements(left: Type, right: Type) -> Type:
    """Collect qualifier vocabulary from every occurrence of a type variable.

    The conjunction seeds qualifiers, not an eager assignment: obligations and
    argument facts still determine the weakest valid instantiation.
    """
    if isinstance(left, (RefinedType, TypeConstructor, TypeVar)) and isinstance(
        right, (RefinedType, TypeConstructor, TypeVar)
    ):
        n, lb, lp = extract_parts(left)
        rn, rb, rp = extract_parts(right)
        if isinstance(lb, TypeConstructor) and isinstance(rb, TypeConstructor):
            lb = TypeConstructor(lb.name, [merge_requirements(a, b) for a, b in zip(lb.args, rb.args)])
        return RefinedType(n, lb, mk_liquid_and(lp, substitution_in_liquid(rp, LiquidVar(n), rn)))
    return left


def erase(ty: Type) -> Type:
    if isinstance(ty, RefinedType):
        return erase(ty.type)
    if isinstance(ty, TypeConstructor):
        return TypeConstructor(ty.name, [erase(a) for a in ty.args])
    if isinstance(ty, AbstractionType):
        return AbstractionType(ty.var_name, erase(ty.var_type), erase(ty.type), multiplicity=ty.multiplicity)
    return ty


@dataclass
class ApplicationState:
    state: ConstraintState
    params: list[tuple[Name, Type]]
    result: Type
    goal: Type
    deferred: list[tuple[Name, Type]] = field(default_factory=list)

    @classmethod
    def start(cls, state: ConstraintState, callee: Type, goal: Type) -> ApplicationState:
        state = state.fork()
        params: list[tuple[Name, Type]] = []
        while isinstance(callee, AbstractionType):
            name = fresh_name("arg")
            params.append((name, callee.var_type))
            callee = substitution_in_type(callee.type, Var(name), callee.var_name)
        return cls(state, params, callee, goal)

    def check(self) -> Status:
        """Check independent result obligations; retain the dependent ones.

        APPFO's bottom domains make obligations mentioning unchosen formals
        vacuous. We retain exactly those obligations for the next step. Nested
        element subtyping (whose scope excludes the formals) is checked now.
        """
        future = {str(n) for n, _ in self.params}
        trial = self.state.fork()
        pending = []
        for clause in split(sub(trial.context, self.result, self.goal)):
            if future.intersection(variables_free_in(clause)):
                pending.append(clause)
            else:
                trial.add(clause)
        trial.pending = tuple(pending)
        status = trial.solve()
        self.state = trial
        if status in (Status.INVALID, Status.EXHAUSTED):
            return status
        if self.params:
            consistency = self.consistency()
            if consistency == Status.INVALID:
                return consistency
        return status

    def consistency(self) -> Status:
        """Fig. 5: ∃ remaining arguments and result satisfying both contracts.

        Existential SAT is only a necessary condition. Unknown/unsupported
        theories retain the application for final verification.
        """
        if any(self.state.unresolved(t) for _, t in self.params):
            return Status.UNKNOWN
        if isinstance(self.result, AbstractionType):
            return Status.UNSUPPORTED
        try:
            value, base, actual = extract_parts(self.result)
            goal_value, goal_base, expected = extract_parts(self.goal)
            if erase(base) != erase(goal_base):
                return Status.UNSUPPORTED
            witness = fresh_name("result")
            predicate = mk_liquid_and(
                substitution_in_liquid(actual, LiquidVar(witness), value),
                substitution_in_liquid(expected, LiquidVar(witness), goal_value),
            )
            context = self.state.context
            for n, ty in self.params:
                # APPHO: a function argument contributes no scalar assumption.
                if not isinstance(ty, AbstractionType):
                    context = context.with_var(n, ty)
            context = context.with_var(witness, RefinedType(witness, base, predicate))
            status = self.state.inhabited(context)
            return Status.INVALID if status == Status.VALID else Status.VALID if status == Status.INVALID else status
        except (AssertionError, NotImplementedError):
            return Status.UNSUPPORTED

    def choose(self, argument: Term) -> ApplicationState:
        """Strengthen with the argument's VC and precise contextual type."""
        (binder, expected), rest = self.params[0], self.params[1:]
        child = self.state.fork()
        unresolved = child.unresolved(expected)
        if unresolved:
            from aeon.typechecking.qualifiers import extract_qualifier_atoms

            _, actual = synth(child.context, argument)
            bindings = match_result(child.resolve(expected), actual, unresolved)
            if bindings is None:
                raise ValueError("Incompatible argument shape")
            for unknown, shape in bindings.items():
                child.type_assignments[unknown] = child.fresh_type(
                    shape, extract_qualifier_atoms(child.context, self.goal)
                )
            expected = child.resolve(expected)
        child.add(check(child.context, argument, expected))
        if isinstance(expected, AbstractionType) or isinstance(argument, Abstraction):
            # APPHO checks the supplied function, without inventing a scalar
            # value for it or leaking its body binders into the result.
            replacement = argument
        else:
            vc, actual = synth(child.context, argument)
            child.add(vc)
            child.bind(binder, actual)
            # Literal/variable substitution preserves the existing dependent
            # argument goal. Other E-terms use the precise contextual witness.
            replacement = argument if isinstance(argument, (Var, Literal)) else Var(binder)
        return ApplicationState(
            child,
            [(n, substitution_in_type(child.resolve(t), replacement, binder)) for n, t in rest],
            substitution_in_type(child.resolve(self.result), replacement, binder),
            self.goal,
            [(n, substitution_in_type(child.resolve(t), replacement, binder)) for n, t in self.deferred],
        )
