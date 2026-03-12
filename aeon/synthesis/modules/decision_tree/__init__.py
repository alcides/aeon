from typing import Callable
from time import monotonic_ns

import numpy as np
from sklearn.tree import DecisionTreeRegressor

from aeon.core.terms import Application, If, Literal, Term, TypeApplication, Var
from aeon.core.types import Type, t_float
from aeon.decorators.api import Metadata
from aeon.synthesis.api import Synthesizer
from aeon.synthesis.uis.api import SynthesisUI
from aeon.typechecking.context import TypingContext, VariableBinder
from aeon.utils.name import Name


def get_elapsed_time(start_time) -> float:
    """The elapsed time since the start in seconds."""
    return (monotonic_ns() - start_time) * 0.000000001


def _get_function_arg_names(ctx: TypingContext, fun_name: Name) -> list[Name]:
    """Extract the function's argument names from the context.

    Arguments are the variables bound after the function itself in the context.
    """
    found_fun = False
    arg_names = []
    for entry in ctx.entries:
        if isinstance(entry, VariableBinder):
            if entry.name.name == fun_name.name:
                found_fun = True
                continue
            if found_fun:
                arg_names.append(entry.name)
    return arg_names


def _tree_to_term(tree: DecisionTreeRegressor, arg_names: list[Name]) -> Term:
    """Convert a fitted sklearn decision tree into nested If-then-else Terms."""
    tree_ = tree.tree_
    feature = tree_.feature
    threshold = tree_.threshold
    value = tree_.value

    def build(node_id: int) -> Term:
        if feature[node_id] == -2:
            # Leaf node: return the predicted value
            leaf_value = float(value[node_id].flatten()[0])
            return Literal(leaf_value, t_float)

        # Internal node: if arg_names[feature_idx] <= threshold then left else right
        feat_idx = feature[node_id]
        thresh = float(threshold[node_id])

        # <= is polymorphic (forall a:B, ...), so apply it to Float first
        le_typed = TypeApplication(Var(Name("<=", 0)), t_float)
        cond = Application(
            Application(le_typed, Var(arg_names[feat_idx])),
            Literal(thresh, t_float),
        )
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

        # Extract argument names from the typing context
        arg_names = _get_function_arg_names(ctx, fun_name)
        if len(arg_names) != X.shape[1]:
            return None

        # Try increasing depths until budget runs out or validation passes
        best_term = None
        best_quality = None
        max_depth_limit = self.max_depth or X.shape[0]

        for depth in range(1, max_depth_limit + 1):
            if get_elapsed_time(start_time) > budget:
                break

            dt = DecisionTreeRegressor(max_depth=depth)
            dt.fit(X, y)

            candidate = _tree_to_term(dt, arg_names)
            elapsed = get_elapsed_time(start_time)

            if validate(candidate):
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
