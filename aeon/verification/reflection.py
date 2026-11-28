"""Bounded, path-sensitive proof by logical evaluation.

Add ground call equations instead of replacing calls. This retains congruence
and induction hypotheses, and never unfolds an undecided recursive branch.
Hitting a resource bound only leaves an obligation unproved.
"""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

from z3 import Solver, is_false, is_true, simplify, Not, unsat

from aeon.compilation.session import current_session
from aeon.core.liquid import LiquidApp, LiquidLiteralBool, LiquidTerm, LiquidVar, liquid_free_vars
from aeon.core.types import AbstractionType, RefinedType, Type
from aeon.core.liquid_ops import mk_liquid_and
from aeon.core.reflection import datatype_operation
from aeon.core.substitutions import substitution_in_liquid
from aeon.utils.name import Name, fresh_counter

if TYPE_CHECKING:
    from aeon.verification.smt import SMTContext


def needs_guarded_evaluation(reflections: dict[str, tuple[tuple[Name, ...], LiquidTerm]]) -> bool:
    dependencies: dict[str, set[str]] = {}
    for name, (_, body) in reflections.items():
        names = liquid_free_vars(body)
        if any(datatype_operation(v) is not None for v in names):
            return True
        dependencies[name] = {str(v) for v in names if str(v) in reflections}
    visited: set[str] = set()
    active: set[str] = set()

    def cyclic(name: str) -> bool:
        if name in active:
            return True
        if name in visited:
            return False
        visited.add(name)
        active.add(name)
        if any(cyclic(child) for child in dependencies[name]):
            return True
        active.remove(name)
        return False

    return any(cyclic(name) for name in dependencies)


def evaluate_reflections(
    ctx: SMTContext, conclusion: LiquidTerm, specializations: dict[tuple[str, tuple[str, ...]], str]
) -> SMTContext:
    from aeon.verification.smt import (
        _specialize_liquid_term,
        mk_funs,
        mk_vars,
        mk_sorts,
        translate_liq,
        constructors_for_env,
        measures_for_env,
        _contract_well_scoped,
        _refined_return_contracts,
    )

    pending: dict[LiquidApp, None] = {}
    done: set[LiquidApp] = set()
    solver = Solver()
    solver.set(timeout=min(100, current_session().options.smt_timeout_ms))

    def within_budget(term: LiquidTerm) -> bool:
        work = [(term, 0)]
        nodes = 0
        while work:
            node, depth = work.pop()
            nodes += 1
            if nodes > 4096 or depth > 96:
                return False
            if isinstance(node, LiquidApp):
                work.extend((arg, depth + 1) for arg in node.args)
        return True

    def collect(term: LiquidTerm) -> None:
        if isinstance(term, LiquidApp):
            if str(term.fun) in ctx.reflected_functions and term not in done:
                pending[term] = None
            for arg in term.args:
                collect(arg)

    def environment():
        sorts = mk_sorts(ctx.sorts)
        variables = mk_vars(ctx.variables, sorts)
        functions = mk_funs(ctx.functions, sorts)
        return variables | functions | constructors_for_env() | measures_for_env()

    def decide(guard: LiquidTerm) -> bool | None:
        if isinstance(guard, LiquidLiteralBool):
            return guard.value
        env = environment()
        translated = translate_liq(guard, env)
        if isinstance(translated, bool):
            return translated
        translated = simplify(translated)
        if is_true(translated):
            return True
        if is_false(translated):
            return False
        solver.reset()
        for premise in ctx.premises:
            solver.add(translate_liq(premise, env))
        for truth, opposite in ((True, Not(translated)), (False, translated)):
            solver.push()
            solver.add(opposite)
            result = solver.check()
            solver.pop()
            if result == unsat:
                return truth
        return None

    def instantiate(term: LiquidTerm, params: list[Name] | tuple[Name, ...], args: list[LiquidTerm]) -> LiquidTerm:
        fresh = [Name("_reflect", fresh_counter.fresh()) for _ in params]
        for param, temporary in zip(params, fresh):
            term = substitution_in_liquid(term, LiquidVar(temporary), param)
        for temporary, argument in zip(fresh, args):
            term = substitution_in_liquid(term, argument, temporary)
        return term

    def domain(call: LiquidApp) -> LiquidTerm:
        signature = ctx.functions[str(call.fun)]
        params: list[Name] = []
        guard: LiquidTerm = LiquidLiteralBool(True)
        current: Type = signature
        refined: list[tuple[Name, LiquidTerm, LiquidTerm]] = []
        for argument in call.args:
            if not isinstance(current, AbstractionType):
                return LiquidLiteralBool(False)
            if isinstance(current.var_type, RefinedType):
                ty = current.var_type
                refined.append((ty.name, ty.refinement, argument))
            params.append(current.var_name)
            current = current.type
        for binder, pre, argument in refined:
            guard = mk_liquid_and(guard, instantiate(pre, [*params, binder], [*call.args, argument]))
        return guard

    def select(term: LiquidTerm) -> LiquidTerm | None:
        if not isinstance(term, LiquidApp):
            return term
        if term.fun == Name("ite", 0) and len(term.args) == 3:
            truth = decide(term.args[0])
            if truth is None:
                collect(term.args[0])
                return None
            return select(term.args[1] if truth else term.args[2])
        args = [select(arg) for arg in term.args]
        if any(arg is None for arg in args):
            return None
        return LiquidApp(term.fun, args, loc=term.loc)

    for premise in ctx.premises:
        collect(premise)
    collect(conclusion)
    # Limit both breadth and depth. In particular f(symbolic_tail) is left
    # opaque until a path fact determines its constructor.
    for _ in range(256):
        progressed = False
        for call in list(pending):
            params, body = ctx.reflected_functions[str(call.fun)]
            if len(params) != len(call.args):
                pending.pop(call)
                continue
            guard = domain(call)
            if not _contract_well_scoped(guard, ctx) or decide(guard) is not True:
                continue
            # Substitution is simultaneous: actual arguments may contain names
            # used as other formals (e.g. swapping two recursive arguments).
            body = instantiate(body, params, call.args)
            if not within_budget(body):
                pending.pop(call)
                continue
            body, functions, reflections = _specialize_liquid_term(
                body, ctx.functions, ctx.variables, ctx.reflected_functions, specializations
            )
            ctx = replace(ctx, functions=functions, reflected_functions=reflections)
            selected = select(body)
            if selected is None:
                continue
            equation = LiquidApp(Name("==", 0), [call, selected])
            ctx = ctx.with_premise(equation)
            for contract in _refined_return_contracts(selected, replace(ctx, premises=[])):
                if contract not in ctx.premises:
                    ctx = ctx.with_premise(contract)
            done.add(call)
            pending.pop(call)
            collect(selected)
            progressed = True
            if len(done) >= 256:
                return ctx
        if not progressed:
            break
    return ctx
