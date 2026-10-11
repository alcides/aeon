"""Portable MLP (NumPy acceleration is optional): predicts subexpression usefulness, not whole programs."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Any

from aeon.synthesis.modules.bustle.signatures import FEATURE_COUNT, SIGNATURE_VERSION

np: Any
try:
    import numpy as _numpy

    np = _numpy
except ImportError:
    np = None


DEFAULT_MODEL = Path(__file__).with_name("model.json")


class GuidanceModel:
    def __init__(self, weights: list[Any], biases: list[Any], provenance: dict[str, Any] | None = None):
        self.weights = weights
        self.biases = biases
        self.provenance = provenance or {}
        if len(weights) != 3 or len(biases) != 3:
            raise ValueError("BUSTLE model must have two hidden layers and an output layer")
        expected = FEATURE_COUNT
        for weight, bias in zip(weights, biases):
            if len(weight) != expected or not len(bias) or any(len(row) != len(bias) for row in weight):
                raise ValueError("incompatible BUSTLE model dimensions")
            if not all(math.isfinite(v) for row in weight for v in row) or not all(math.isfinite(v) for v in bias):
                raise ValueError("non-finite BUSTLE model parameters")
            expected = len(bias)
        if expected != 1:
            raise ValueError("BUSTLE model must predict one probability")

    @classmethod
    def initialize(cls, seed: int = 0) -> GuidanceModel:
        if np is None:
            raise ValueError("training BUSTLE requires NumPy; install Aeon[ml]")
        rng = np.random.default_rng(seed)
        widths = (FEATURE_COUNT, 32, 16, 1)
        weights = [rng.normal(0, np.sqrt(2 / left), (left, right)) for left, right in zip(widths, widths[1:])]
        return cls(weights, [np.zeros(width) for width in widths[1:]])

    def predict(self, features: Any) -> Any:
        if np is None:
            predictions: list[float] = []
            for row in features:
                if len(row) != FEATURE_COUNT or not all(math.isfinite(v) for v in row):
                    raise ValueError("incompatible BUSTLE property signature")
                activation = list(row)
                for layer, (weight, bias) in enumerate(zip(self.weights, self.biases)):
                    activation = [
                        float(b) + sum(v * w[j] for v, w in zip(activation, weight)) for j, b in enumerate(bias)
                    ]
                    if layer < 2:
                        activation = [max(0, v) for v in activation]
                predictions.append(1 / (1 + math.exp(-max(-40, min(40, activation[0])))))
            return predictions
        x = np.asarray(features, dtype=np.float64)
        if x.ndim != 2 or x.shape[1] != FEATURE_COUNT or not np.isfinite(x).all():
            raise ValueError("incompatible BUSTLE property signature")
        for weight, bias in zip(self.weights[:-1], self.biases[:-1]):
            x = np.maximum(0, x @ weight + bias)
        logits = x @ self.weights[-1] + self.biases[-1]
        return (1 / (1 + np.exp(-np.clip(logits, -40, 40)))).ravel()

    def fit(self, features: Any, labels: Any, *, epochs: int = 30, seed: int = 0) -> list[float]:
        """Mini-batch Adam with binary cross-entropy; requires NumPy only for training."""
        if np is None:
            raise ValueError("training BUSTLE requires NumPy; install Aeon[ml]")
        rng = np.random.default_rng(seed)
        x = np.asarray(features, dtype=np.float64)
        y = np.asarray(labels, dtype=np.float64).reshape(-1, 1)
        if x.shape != (len(y), FEATURE_COUNT) or not len(y) or not np.isfinite(x).all():
            raise ValueError("invalid BUSTLE training features")
        if not np.isin(y, [0, 1]).all() or epochs < 1:
            raise ValueError("invalid BUSTLE labels or epoch count")
        params = [*self.weights, *self.biases]
        moments = [np.zeros_like(p) for p in params]
        velocities = [np.zeros_like(p) for p in params]
        losses: list[float] = []
        step = 0
        for _ in range(epochs):
            order = rng.permutation(len(y))
            for start in range(0, len(y), 128):
                indices = order[start : start + 128]
                activations = [x[indices]]
                for weight, bias in zip(self.weights[:-1], self.biases[:-1]):
                    activations.append(np.maximum(0, activations[-1] @ weight + bias))
                logits = activations[-1] @ self.weights[-1] + self.biases[-1]
                prediction = 1 / (1 + np.exp(-np.clip(logits, -40, 40)))
                delta = (prediction - y[indices]) / len(indices)
                weight_grads: list[np.ndarray] = []
                bias_grads: list[np.ndarray] = []
                for layer in reversed(range(3)):
                    weight_grads.insert(0, activations[layer].T @ delta)
                    bias_grads.insert(0, delta.sum(axis=0))
                    if layer:
                        delta = (delta @ self.weights[layer].T) * (activations[layer] > 0)
                step += 1
                for param, moment, velocity, grad in zip(params, moments, velocities, [*weight_grads, *bias_grads]):
                    moment *= 0.9
                    moment += 0.1 * grad
                    velocity *= 0.999
                    velocity += 0.001 * grad * grad
                    param -= 0.001 * (moment / (1 - 0.9**step)) / (np.sqrt(velocity / (1 - 0.999**step)) + 1e-8)
            probabilities = np.clip(self.predict(x), 1e-8, 1 - 1e-8)
            targets = y.ravel()
            losses.append(float(-(targets * np.log(probabilities) + (1 - targets) * np.log(1 - probabilities)).mean()))
        return losses

    def save(self, path: str | Path) -> None:
        data = {
            "signature_version": SIGNATURE_VERSION,
            "feature_count": FEATURE_COUNT,
            "weights": [weight.tolist() if hasattr(weight, "tolist") else weight for weight in self.weights],
            "biases": [bias.tolist() if hasattr(bias, "tolist") else bias for bias in self.biases],
            "provenance": self.provenance,
        }
        Path(path).write_text(json.dumps(data, separators=(",", ":")) + "\n", encoding="utf-8")

    @classmethod
    def load(cls, path: str | Path = DEFAULT_MODEL) -> GuidanceModel:
        data = json.loads(Path(path).read_text(encoding="utf-8"))
        if data.get("signature_version") != SIGNATURE_VERSION or data.get("feature_count") != FEATURE_COUNT:
            raise ValueError("incompatible BUSTLE signature schema")
        if not data.get("provenance", {}).get("trained"):
            raise ValueError("BUSTLE checkpoint does not declare trained guidance")
        return cls(
            [np.asarray(w, dtype=np.float64) if np is not None else w for w in data["weights"]],
            [np.asarray(b, dtype=np.float64) if np is not None else b for b in data["biases"]],
            data["provenance"],
        )
