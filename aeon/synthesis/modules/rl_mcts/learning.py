"""Replay data and XGBoost policy/value models; no learning during inference."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
import json
from pathlib import Path
from typing import Any

from aeon.synthesis.modules.rl_mcts.features import Syntax, policy_features, value_features
from aeon.synthesis.modules.rl_mcts.search import Guidance, SearchResult, bounded_prediction


@dataclass
class Replay:
    values: list[tuple[list[float], float]]
    policies: list[tuple[list[float], float]]


def training_data(spec: Syntax, result: SearchResult[Any], bins: int = 4093) -> Replay:
    if result.solution is None:
        return Replay([(value_features(spec, n.tree, bins), 0.0) for n in result.nodes if n.visits], [])
    path = result.solution.path()
    values = [(value_features(spec, n.tree, bins), 0.9 ** (len(path) - i - 1)) for i, n in enumerate(path)]
    policies = []
    for parent, child in zip(path, path[1:]):
        visits = sum(c.visits for c in parent.children)
        policies.append((policy_features(spec, parent.tree, child.tree, bins), child.visits / max(1, visits)))
    return Replay(values, policies)


class LearnedGuidance:
    def __init__(self, value_model: Any, policy_model: Any, bins: int = 4093):
        self.value_model = value_model
        self.policy_model = policy_model
        self.bins = bins

    @staticmethod
    def _predict(model: Any, vector: list[float]) -> float:
        import numpy as np

        return bounded_prediction(float(model.predict(np.asarray([vector], dtype=np.float32))[0]))

    def value(self, spec: Syntax, state: Syntax, holes: int) -> float:
        return self._predict(self.value_model, value_features(spec, state, self.bins))

    def policy(self, spec: Syntax, state: Syntax, child: Syntax) -> float:
        return self._predict(self.policy_model, policy_features(spec, state, child, self.bins))

    @classmethod
    def fit(cls, replay: Replay, *, bins: int = 4093, seed: int = 0, estimators: int = 64) -> LearnedGuidance:
        import numpy as np

        XGBRegressor = _regressor()
        if not replay.values or not replay.policies:
            raise ValueError("training requires value samples and at least one successful policy path")

        def fit_model(samples: list[tuple[list[float], float]], width: int, depth: int) -> Any:
            if any(len(x) != width for x, _ in samples):
                raise ValueError("training feature width does not match hash base")
            model = XGBRegressor(
                n_estimators=estimators,
                max_depth=depth,
                objective="reg:squarederror",
                tree_method="hist",
                n_jobs=1,
                random_state=seed,
            )
            model.fit(np.asarray([x for x, _ in samples], dtype=np.float32), np.asarray([y for _, y in samples]))
            return model

        return cls(fit_model(replay.values, 2 * bins, 20), fit_model(replay.policies, 3 * bins, 25), bins)

    def save(self, directory: str | Path) -> None:
        directory = Path(directory)
        directory.mkdir(parents=True, exist_ok=True)
        self.value_model.save_model(directory / "value.ubj")
        self.policy_model.save_model(directory / "policy.ubj")
        (directory / "manifest.json").write_text(json.dumps({"format": 1, "bins": self.bins}), encoding="utf-8")

    @classmethod
    def load(cls, directory: str | Path) -> LearnedGuidance:
        directory = Path(directory)
        manifest = json.loads((directory / "manifest.json").read_text(encoding="utf-8"))
        if manifest.get("format") != 1 or not isinstance(manifest.get("bins"), int) or manifest["bins"] < 1:
            raise ValueError("unsupported RL-MCTS model manifest")
        XGBRegressor = _regressor()
        value, policy = XGBRegressor(), XGBRegressor()
        value.load_model(directory / "value.ubj")
        policy.load_model(directory / "policy.ubj")
        bins = manifest["bins"]
        if value.n_features_in_ != 2 * bins or policy.n_features_in_ != 3 * bins:
            raise ValueError("RL-MCTS model feature widths do not match manifest")
        return cls(value, policy, bins)


def _regressor() -> Any:
    try:
        from xgboost import XGBRegressor
    except ImportError as exc:
        raise ImportError("learned rl_mcts requires pip install 'AeonLang[synthesis-rl]'") from exc
    return XGBRegressor


def train(
    problems: Sequence[Callable[[Guidance | None], tuple[Syntax, SearchResult[Any]]]],
    *,
    iterations: int = 2,
    history: int = 4,
    bins: int = 4093,
    seed: int = 0,
    estimators: int = 64,
) -> tuple[LearnedGuidance, list[Replay]]:
    """Self-improvement loop; problem callbacks run search, never supply answers.

    Iteration zero uses the paper's default guidance. Every later iteration
    reruns the training problems with newly fitted models and accumulates the
    last four iterations' replay data. Held-out problems must not be passed in.
    """
    if iterations < 1 or history < 1 or not problems:
        raise ValueError("training needs positive iterations/history and nonempty problems")
    model: LearnedGuidance | None = None
    replays: list[Replay] = []
    for _ in range(iterations):
        values: list[tuple[list[float], float]] = []
        policies: list[tuple[list[float], float]] = []
        for problem in problems:
            spec, result = problem(model)
            replay = training_data(spec, result, bins)
            values.extend(replay.values)
            policies.extend(replay.policies)
        replays.append(Replay(values, policies))
        recent = replays[-history:]
        combined = Replay([v for r in recent for v in r.values], [p for r in recent for p in r.policies])
        model = LearnedGuidance.fit(combined, bins=bins, seed=seed, estimators=estimators)
    assert model is not None
    return model, replays
