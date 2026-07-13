from typing import Callable
from time import monotonic_ns

import numpy as np
from sklearn.tree import DecisionTreeRegressor

from aeon.core.terms import Application, If, Literal, Term, TypeApplication, Var
from aeon.core.types import Type, t_float, t_int
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.modules.tdsyn.helpers import base_type_of
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.name import Name


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


def _get_function_args(ctx: TypingContext, fun_name: Name) -> list[tuple[Name, Type]]:
    """Extract the function's argument names and types from the context.

    Arguments are the variables bound after the function itself in the context.
    """
    found_fun = False
    args: list[tuple[Name, Type]] = []
    for entry in ctx.entries:
        if isinstance(entry, VariableBinder):
            if entry.name.name == fun_name.name:
                found_fun = True
                continue
            if found_fun:
                args.append((entry.name, entry.type))
    return args


def _numeric_literal(value: float, ty: Type) -> Term:
    """Build a numeric literal with the correct base type (Int or Float)."""
    if base_type_of(ty) == t_int:
        return Literal(int(round(value)), t_int)
    return Literal(float(value), t_float)


def _comparison_operand(arg_name: Name, arg_ty: Type) -> Term:
    """Build the left-hand side of a tree split comparison."""
    if base_type_of(arg_ty) == t_int:
        return Application(Var(Name("toFloat", 0)), Var(arg_name))
    return Var(arg_name)


def _split_condition(arg_name: Name, arg_ty: Type, threshold: float) -> Term:
    """``<=`` comparison preserving sklearn's floating-point split threshold."""
    le_typed = TypeApplication(Var(Name("<=", 0)), t_float)
    return Application(
        Application(le_typed, _comparison_operand(arg_name, arg_ty)),
        Literal(threshold, t_float),
    )


def _tree_to_term(
    tree: DecisionTreeRegressor,
    arg_names: list[Name],
    return_type: Type,
    arg_types: list[Type],
) -> Term:
    """Convert a fitted sklearn decision tree into nested If-then-else Terms."""
    tree_ = tree.tree_
    feature = tree_.feature
    threshold = tree_.threshold
    value = tree_.value

    def build(node_id: int) -> Term:
        if feature[node_id] == -2:
            leaf_value = float(value[node_id].flatten()[0])
            return _numeric_literal(leaf_value, return_type)

        feat_idx = feature[node_id]
        thresh = float(threshold[node_id])

        cond = _split_condition(arg_names[feat_idx], arg_types[feat_idx], thresh)
        then_branch = build(tree_.children_left[node_id])
        else_branch = build(tree_.children_right[node_id])
        return If(cond, then_branch, else_branch)

    return build(0)


class DecisionTreeSynthesizer(Synthesizer):
    def __init__(self, max_depth: int | None = None):
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
        output_value: Callable[[Term], object] | None = None,
    ) -> Term:
        assert isinstance(ctx, TypingContext)
        assert isinstance(type, Type)

        start_time = monotonic_ns()

        # Extract training data from metadata (match by name string since IDs
        # may differ between parsing and binding phases)
        current_metadata = {}
        for key, val in metadata.items():
            if isinstance(val, dict) and key.name == fun_name.name:
                current_metadata = val
                break
        training_data: list[list[float]] = current_metadata.get("training_data", [])
        if not training_data:
            return None

        data = np.array(training_data)
        X = data[:, :-1]
        y = data[:, -1]

        # Extract argument names/types from the typing context (the hole type
        # is the return type only, not the full function type).
        fun_args = _get_function_args(ctx, fun_name)
        arg_names = [name for name, _ in fun_args]
        if len(arg_names) != X.shape[1]:
            return None
        arg_types = [aty for _, aty in fun_args]
        return_type = type

        # Try increasing depths until budget runs out or validation passes
        has_goals = bool(current_metadata.get("goals"))
        best_term = None
        best_quality = None
        max_depth_limit = self.max_depth or X.shape[0]

        for depth in range(1, max_depth_limit + 1):
            if get_elapsed_time(start_time) > budget:
                break

            dt = DecisionTreeRegressor(max_depth=depth)
            dt.fit(X, y)

            candidate = _tree_to_term(dt, arg_names, return_type, arg_types)
            elapsed = get_elapsed_time(start_time)

            if validate(candidate):
                # No optimization goals — return immediately
                if not has_goals:
                    ui.register(candidate, [], elapsed, True)
                    return candidate
                try:
                    quality = evaluate(candidate)
                    is_best = best_quality is None or all(q <= bq for q, bq in zip(quality, best_quality))
                    ui.register(candidate, quality, elapsed, is_best)
                    if is_best:
                        best_term = candidate
                        best_quality = quality
                    # Perfect fit: no need to try deeper trees
                    if all(q == 0.0 for q in quality):
                        break
                except Exception:
                    ui.register(candidate, None, elapsed, False)
            else:
                ui.register(candidate, None, elapsed, False)

        return best_term
