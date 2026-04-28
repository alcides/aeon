"""SMT-guided synthesizer.

Builds expression trees top-down:
- Non-SMT types: look for constructors/functions in the context, recurse into their arguments.
- SMT types (Int, Bool, Float): create a z3 placeholder variable and add any refinement
  constraints to the solver.

After the tree is built, solve the z3 constraints and replace placeholders with concrete
literal values, then validate the result.

The synthesizer loops until the time budget is exhausted, shuffling the context variable
ordering on each attempt to explore different term structures.
"""

from __future__ import annotations

import random
import time
from typing import Callable

import z3
from loguru import logger

from aeon.core.liquid import (
    LiquidApp,
    LiquidHole,
    LiquidLiteralBool,
    LiquidLiteralFloat,
    LiquidLiteralInt,
    LiquidLiteralString,
    LiquidTerm,
    LiquidVar,
)
from aeon.core.substitutions import substitute_vartype
from aeon.core.terms import Application, Literal, Term, TypeApplication, Var
from aeon.core.types import (
    AbstractionType,
    LiquidHornApplication,
    RefinedType,
    RefinementPolymorphism,
    Type,
    TypeConstructor,
    TypePolymorphism,
    TypeVar,
    t_bool,
    t_float,
    t_int,
)
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer, SynthesisNotSuccessful
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, UninterpretedBinder
from aeon.utils.name import Name, fresh_counter
from aeon.verification.smt import base_functions, make_variable

# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_SMT_BASE_NAMES = {"Int", "Bool", "Float"}


def _is_better(v1: list[float], v2: list[float]) -> bool:
    """True if v1 dominates v2 (all components strictly less)."""
    if not v2:
        return True
    return all(x < y for x, y in zip(v1, v2))


def _is_smt_base(ty: Type) -> bool:
    return isinstance(ty, TypeConstructor) and ty.name.name in _SMT_BASE_NAMES


def _base_type(ty: Type) -> Type:
    """Strip a RefinedType wrapper to get the base TypeConstructor/TypeVar."""
    if isinstance(ty, RefinedType):
        return ty.type
    return ty


def _return_base_type(ty: Type) -> Type | None:
    """Walk an AbstractionType chain to its final return, strip refinement."""
    current: Type = ty
    while isinstance(current, AbstractionType):
        current = current.type
    while isinstance(current, TypePolymorphism):
        current = current.body
    return _base_type(current)


def _get_params(ty: Type) -> list[tuple[Name, Type]]:
    """Return (var_name, var_type) for each parameter of a function type."""
    params: list[tuple[Name, Type]] = []
    current: Type = ty
    while isinstance(current, TypePolymorphism):
        current = current.body
    while isinstance(current, AbstractionType):
        params.append((current.var_name, current.var_type))
        current = current.type
    return params


# ---------------------------------------------------------------------------
# Refinement translation
# ---------------------------------------------------------------------------


def _translate_liq(
    t: LiquidTerm,
    variables: dict[str, object],
    uninterp_ctx: dict[str, object],
) -> object | None:
    """Translate a liquid term to a z3 expression.

    Returns None if translation is not possible (e.g. horn application).
    """
    match t:
        case LiquidLiteralBool(b):
            return b
        case LiquidLiteralInt(i):
            return i
        case LiquidLiteralFloat(f):
            return f
        case LiquidLiteralString():
            return None  # strings not useful in arithmetic constraints
        case LiquidVar(name):
            key = str(name)
            if key in variables:
                return variables[key]
            if key in uninterp_ctx:
                return uninterp_ctx[key]
            return None
        case LiquidApp(fun_name, args):
            # Try built-in operators first
            fun = base_functions.get(fun_name.name, None)
            if fun is None:
                # Try uninterpreted function from context
                fun = uninterp_ctx.get(str(fun_name), None)
            if fun is None:
                return None
            translated = [_translate_liq(a, variables, uninterp_ctx) for a in args]
            if any(a is None for a in translated):
                return None
            try:
                return fun(*translated)
            except Exception:
                return None
        case LiquidHole():
            return None
        case LiquidHornApplication():
            return None
        case _:
            return None


def _build_uninterp_ctx(ctx: TypingContext) -> dict[str, object]:
    """Build a dict of uninterpreted (and abstraction) functions as z3 objects."""
    result: dict[str, object] = {}
    for entry in ctx.entries:
        if isinstance(entry, UninterpretedBinder):
            try:
                z3_fun = make_variable(str(entry.name), entry.type)
                result[str(entry.name)] = z3_fun
            except Exception:
                pass
    return result


# ---------------------------------------------------------------------------
# Polymorphic instantiation
# ---------------------------------------------------------------------------


def _unify_types(ty1: Type, ty2: Type, forall_names: set[Name], bindings: dict[Name, Type]) -> bool:
    """Try to unify ty1 (may contain TypeVars from forall_names) with concrete ty2."""
    if isinstance(ty1, TypeVar) and ty1.name in forall_names:
        if ty1.name in bindings:
            return bindings[ty1.name] == ty2
        bindings[ty1.name] = ty2
        return True
    if isinstance(ty1, TypeConstructor) and isinstance(ty2, TypeConstructor):
        if ty1.name != ty2.name or len(ty1.args) != len(ty2.args):
            return False
        return all(_unify_types(a1, a2, forall_names, bindings) for a1, a2 in zip(ty1.args, ty2.args))
    return ty1 == ty2


def _try_instantiate_poly(
    var_ty: TypePolymorphism, target_base: TypeConstructor
) -> tuple[Type, list[Type]] | None:
    """Try to instantiate a polymorphic type so its return type matches target_base.

    Returns (instantiated_body, type_apps) or None if unification fails.
    """
    foralls: list[Name] = []
    current: Type = var_ty
    while isinstance(current, TypePolymorphism):
        foralls.append(current.name)
        current = current.body
    if isinstance(current, RefinementPolymorphism):
        return None

    # Walk to return type
    ret: Type = current
    while isinstance(ret, AbstractionType):
        ret = ret.type
    ret_base = _base_type(ret)

    bindings: dict[Name, Type] = {}
    if not _unify_types(ret_base, target_base, set(foralls), bindings):
        return None
    # All foralls must be bound
    if not all(f in bindings for f in foralls):
        return None

    body = current
    type_apps: list[Type] = []
    for f in foralls:
        body = substitute_vartype(body, bindings[f], f)
        type_apps.append(bindings[f])
    return (body, type_apps)


# ---------------------------------------------------------------------------
# SMTSynthesizer
# ---------------------------------------------------------------------------


class SMTSynthesizer(Synthesizer):
    """Synthesizer that uses z3 to find concrete values for SMT-typed holes.

    For non-SMT types (e.g. Board, Coordinate), it looks in the typing context
    for constructor functions and recursively synthesizes their arguments.
    """

    def __init__(self, max_depth: int = 5) -> None:
        self.max_depth = max_depth

    def synthesize(
        self,
        ctx: TypingContext,
        type: Type,
        validate: Callable[[Term], bool],
        evaluate: Callable[[Term], list[float]],
        fun_name: Name,
        metadata: Metadata,
        budget: float = 60,
        ui: SynthesisUI = SynthesisUI(),
    ) -> Term:
        current_meta = metadata.get(fun_name, {})
        hidden: set[str] = {n.name for n in current_meta.get("hide", [])}
        uninterp_ctx = _build_uninterp_ctx(ctx)

        # Build z3 context variables (shared across attempts — only depends on ctx)
        ctx_z3_vars: dict[str, object] = {}
        ctx_constraints: list[object] = []
        for name, ty in ctx.concrete_vars():
            base = _base_type(ty)
            if _is_smt_base(base):
                assert isinstance(base, TypeConstructor)
                z3_var = make_variable(str(name), base)
                ctx_z3_vars[str(name)] = z3_var
                if isinstance(ty, RefinedType):
                    all_vars = {**ctx_z3_vars, str(ty.name): z3_var}
                    constraint = _translate_liq(ty.refinement, all_vars, uninterp_ctx)
                    if constraint is not None and not isinstance(constraint, bool):
                        ctx_constraints.append(constraint)

        has_goals = bool(current_meta.get("goals"))
        rng = random.Random(42)
        best_score: list[float] = []
        best_term: Term | None = None
        start_time = time.time()
        deadline = start_time + budget
        attempt = 0

        while time.time() < deadline:
            attempt += 1

            solver = z3.Solver()
            solver.set(timeout=min(10_000, int((deadline - time.time()) * 1000)))
            for c in ctx_constraints:
                solver.add(c)

            holes: dict[Name, tuple[object, TypeConstructor]] = {}

            term = self._build_term(
                ctx=ctx,
                target_type=type,
                fun_name=fun_name,
                hidden=hidden,
                solver=solver,
                holes=holes,
                ctx_z3_vars=ctx_z3_vars,
                uninterp_ctx=uninterp_ctx,
                depth=0,
                rng=rng if attempt > 1 else None,
            )

            if term is None:
                continue

            result = solver.check()
            if result != z3.sat:
                continue

            model = solver.model()
            concrete_term = self._replace_holes(term, holes, model)

            try:
                if not validate(concrete_term):
                    ui.register(concrete_term, "Invalid", time.time() - start_time, False)
                    continue
            except Exception:
                ui.register(concrete_term, "Invalid", time.time() - start_time, False)
                continue

            # No optimization goals — return immediately
            if not has_goals:
                ui.register(concrete_term, [], time.time() - start_time, True)
                return concrete_term

            try:
                score = evaluate(concrete_term)
            except Exception:
                ui.register(concrete_term, "Invalid", time.time() - start_time, False)
                continue

            elapsed = time.time() - start_time
            is_best = not best_score or _is_better(score, best_score)
            if is_best:
                best_score = score
                best_term = concrete_term
            ui.register(concrete_term, score, elapsed, is_best)

        if best_term is not None:
            return best_term
        raise SynthesisNotSuccessful("SMTSynthesizer: no valid candidate found within budget")

    def _build_term(
        self,
        ctx: TypingContext,
        target_type: Type,
        fun_name: Name,
        hidden: set[str],
        solver: z3.Solver,
        holes: dict[Name, tuple[object, TypeConstructor]],
        ctx_z3_vars: dict[str, object],
        uninterp_ctx: dict[str, object],
        depth: int,
        rng: random.Random | None = None,
    ) -> Term | None:
        if depth > self.max_depth:
            return None

        base = _base_type(target_type)

        if _is_smt_base(base):
            assert isinstance(base, TypeConstructor)
            # Create a fresh z3 hole
            hole_name = Name(f"__smt_hole_{fresh_counter.fresh()}", 0)
            z3_var = make_variable(str(hole_name), base)
            holes[hole_name] = (z3_var, base)

            # Add refinement constraint
            if isinstance(target_type, RefinedType):
                binder_str = str(target_type.name)
                all_vars = {**ctx_z3_vars, binder_str: z3_var}
                constraint = _translate_liq(target_type.refinement, all_vars, uninterp_ctx)
                if constraint is not None and not isinstance(constraint, bool):
                    solver.add(constraint)

            return Var(hole_name)

        # Non-SMT: find a function in ctx whose return base type matches
        if not isinstance(base, TypeConstructor):
            return None

        target_name = base.name.name

        _SYSTEM_NAMES = {"native", "native_import", "print"}

        # Shuffle context variable order to explore different terms on each attempt
        ctx_vars = list(ctx.concrete_vars())
        if rng is not None:
            rng.shuffle(ctx_vars)

        for var_name, var_ty in ctx_vars:
            # Skip hidden variables (compare by base name string, not id)
            if var_name.name in hidden:
                continue
            # Skip the function being synthesized (no self-recursion)
            if var_name == fun_name:
                continue
            # Skip internal/system names
            if var_name.name.startswith("__internal__") or var_name.name in _SYSTEM_NAMES:
                continue
            # Try to instantiate polymorphic functions
            effective_ty: Type = var_ty
            type_apps: list[Type] = []
            if isinstance(var_ty, TypePolymorphism):
                result = _try_instantiate_poly(var_ty, base)
                if result is None:
                    continue
                effective_ty, type_apps = result

            # Skip non-functions (plain values of non-SMT type could be vars)
            if not isinstance(effective_ty, AbstractionType):
                # A plain variable (non-function) whose base type matches
                plain_base = _base_type(effective_ty)
                if isinstance(plain_base, TypeConstructor) and plain_base == base:
                    head: Term = Var(var_name)
                    for ta in type_apps:
                        head = TypeApplication(head, ta)
                    return head
                continue

            ret_base = _return_base_type(effective_ty)
            if not isinstance(ret_base, TypeConstructor):
                continue
            if ret_base != base:
                continue

            # This function can produce the needed type — try to build args
            params = _get_params(effective_ty)
            args: list[Term] = []
            success = True

            for _param_name, param_type in params:
                arg = self._build_term(
                    ctx=ctx,
                    target_type=param_type,
                    fun_name=fun_name,
                    hidden=hidden,
                    solver=solver,
                    holes=holes,
                    ctx_z3_vars=ctx_z3_vars,
                    uninterp_ctx=uninterp_ctx,
                    depth=depth + 1,
                    rng=rng,
                )
                if arg is None:
                    success = False
                    break
                args.append(arg)

            if success:
                head: Term = Var(var_name)
                for ta in type_apps:
                    head = TypeApplication(head, ta)
                for arg in args:
                    head = Application(head, arg)
                return head

        return None

    def _replace_holes(
        self,
        term: Term,
        holes: dict[Name, tuple[object, TypeConstructor]],
        model: z3.ModelRef,
    ) -> Term:
        if isinstance(term, Var):
            if term.name in holes:
                z3_var, base = holes[term.name]
                value = model.eval(z3_var, model_completion=True)
                python_val = self._z3_to_python(value, base)
                return Literal(python_val, base)
            return term
        if isinstance(term, Application):
            return Application(
                self._replace_holes(term.fun, holes, model),
                self._replace_holes(term.arg, holes, model),
            )
        return term

    @staticmethod
    def _z3_to_python(z3_val: object, base: TypeConstructor) -> object:
        try:
            if base == t_int and hasattr(z3_val, "as_long"):
                return z3_val.as_long()
            if base == t_bool:
                return bool(z3_val)
            if base == t_float and hasattr(z3_val, "as_decimal"):
                return float(z3_val.as_decimal(10).rstrip("?"))
        except Exception:
            pass
        return 0
