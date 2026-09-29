"""Native helpers for the Aeon MNIST neuroevolution synthesis benchmark.

Evolves a small MLP *topology* (hidden widths + activations) with Aeon's
synthesizer. Multi-objective fitness for an architecture ``Arch`` is:

    [1 - test_accuracy, n_hidden_units]

after a short NumPy SGD run on a downsampled MNIST subset
(``@multi_minimize_float``). A legacy scalar ``fitness`` keeps the old
weighted sum for comparison. Training intentionally uses NumPy (not
PyTorch) so each synthesis worker process stays under Aeon's ~1s evaluation
timeout — importing ``torch`` alone exceeds that budget. The surface ``NN``
library remains PyTorch-backed; this module is only the synthesis oracle.

An ``Arch`` value arrives from Aeon as a nested-tuple ADT chain, e.g.

    ('Arch_arch_relu32', ('Arch_arch_tanh16', ('Arch_arch_out',)))

meaning hidden layers ``relu(32) -> tanh(16) -> linear(10)`` on a
``INPUT_DIM``-feature input (14×14 downsampled MNIST by default).
"""

from __future__ import annotations

import hashlib
from functools import lru_cache
from pathlib import Path
from typing import Any

import numpy as np

# 14×14 downsampled pixels keep each fitness eval cheap enough for GP.
DOWNSAMPLE = 2
INPUT_DIM = (28 // DOWNSAMPLE) ** 2  # 196
N_CLASSES = 10

N_TRAIN = 2000
N_TEST = 500
TRAIN_EPOCHS = 8
LEARNING_RATE = 0.05
BATCH_SIZE = 64
COMPLEXITY_WEIGHT = 5e-5
MAX_HIDDEN = 6
SEED = 0

# Constructor tag -> (activation, width). Tags match Aeon's ADT encoding.
_LAYER_OF: dict[str, tuple[str, int]] = {
    "Arch_arch_relu16": ("relu", 16),
    "Arch_arch_relu32": ("relu", 32),
    "Arch_arch_relu64": ("relu", 64),
    "Arch_arch_tanh16": ("tanh", 16),
    "Arch_arch_tanh32": ("tanh", 32),
    "Arch_arch_sigmoid16": ("sigmoid", 16),
    "Arch_arch_sigmoid32": ("sigmoid", 32),
}


def _flatten_arch(arch: Any) -> list[tuple[str, int]]:
    """Flatten the Aeon Arch tuple chain into ``[(act, width), ...]`` hiddens."""
    layers: list[tuple[str, int]] = []
    node = arch
    while isinstance(node, tuple) and node and node[0] != "Arch_arch_out":
        tag = str(node[0])
        if tag not in _LAYER_OF:
            raise ValueError(f"unknown Arch constructor: {tag!r}")
        layers.append(_LAYER_OF[tag])
        node = node[1]
        if len(layers) >= MAX_HIDDEN:
            break
    return layers


def _downsample_mnist(X: np.ndarray, factor: int) -> np.ndarray:
    """Average-pool 28×28 images by ``factor`` (must divide 28)."""
    n = X.shape[0]
    side = 28 // factor
    imgs = X.reshape(n, 28, 28)
    imgs = imgs.reshape(n, side, factor, side, factor).mean(axis=(2, 4))
    return imgs.reshape(n, side * side).astype(np.float32)


@lru_cache(maxsize=1)
def load_mnist_subset() -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    """Return ``(X_train, y_train, X_test, y_test)`` for the fixed subset.

    Prefers the committed ``mnist_subset.npz`` next to this file so each
    synthesis worker process can load data in milliseconds (no OpenML fetch).
    Falls back to downloading MNIST via scikit-learn when the cache is absent.
    """
    cache = Path(__file__).resolve().parent / "mnist_subset.npz"
    if cache.is_file():
        data = np.load(cache)
        return data["X_train"], data["y_train"], data["X_test"], data["y_test"]

    from sklearn.datasets import fetch_openml

    raw = fetch_openml("mnist_784", version=1, as_frame=False, parser="auto")
    X = raw.data.astype(np.float32) / 255.0
    y = raw.target.astype(np.int64)
    X = _downsample_mnist(X, DOWNSAMPLE)

    rng = np.random.default_rng(SEED)
    train_idx: list[int] = []
    test_idx: list[int] = []
    per_train = N_TRAIN // N_CLASSES
    per_test = N_TEST // N_CLASSES
    for c in range(N_CLASSES):
        cls = np.where(y == c)[0]
        pick = rng.choice(cls, size=per_train + per_test, replace=False)
        train_idx.extend(pick[:per_train].tolist())
        test_idx.extend(pick[per_train:].tolist())
    rng.shuffle(train_idx)
    rng.shuffle(test_idx)
    return X[train_idx], y[train_idx], X[test_idx], y[test_idx]


def _activate(name: str, z: np.ndarray) -> np.ndarray:
    if name == "relu":
        return np.maximum(z, 0.0)
    if name == "sigmoid":
        return 1.0 / (1.0 + np.exp(-np.clip(z, -40.0, 40.0)))
    if name == "tanh":
        return np.tanh(z)
    return z


def _activate_deriv(name: str, z: np.ndarray, a: np.ndarray) -> np.ndarray:
    if name == "relu":
        return (z > 0.0).astype(np.float32)
    if name == "sigmoid":
        return a * (1.0 - a)
    if name == "tanh":
        return 1.0 - a * a
    return np.ones_like(z, dtype=np.float32)


def _init_mlp(widths: list[int], acts: list[str], rng: np.random.Generator):
    """Return ``[(W, b, act), ...]`` with Xavier/He-style initialisation."""
    layers = []
    for i, act in enumerate(acts):
        nin, nout = widths[i], widths[i + 1]
        if act == "relu":
            std = np.sqrt(2.0 / nin)
        else:
            std = np.sqrt(1.0 / nin)
        W = rng.normal(0.0, std, size=(nout, nin)).astype(np.float32)
        b = np.zeros(nout, dtype=np.float32)
        layers.append((W, b, act))
    return layers


def _forward(layers, x: np.ndarray) -> np.ndarray:
    a = x
    for W, b, act in layers:
        a = _activate(act, a @ W.T + b)
    return a


def _train_ce(layers, X: np.ndarray, y: np.ndarray, rng: np.random.Generator) -> None:
    """In-place mini-batch SGD on softmax cross-entropy (mutates ``layers``)."""
    n = X.shape[0]
    for _ in range(TRAIN_EPOCHS):
        order = rng.permutation(n)
        for start in range(0, n, BATCH_SIZE):
            idx = order[start : start + BATCH_SIZE]
            xb = X[idx]
            yb = y[idx]

            # Forward with cache.
            activations = [xb]
            pres = []
            a = xb
            for W, b, act in layers:
                z = a @ W.T + b
                a = _activate(act, z)
                pres.append((z, act))
                activations.append(a)

            logits = activations[-1]
            # Stable softmax.
            z = logits - logits.max(axis=1, keepdims=True)
            exp = np.exp(z)
            probs = exp / exp.sum(axis=1, keepdims=True)
            # One-hot targets.
            target = np.zeros_like(probs)
            target[np.arange(len(yb)), yb] = 1.0
            delta = (probs - target) / max(1, len(yb))

            # Backprop.
            for layer_i in range(len(layers) - 1, -1, -1):
                z, act = pres[layer_i]
                delta = delta * _activate_deriv(act, z, activations[layer_i + 1])
                gW = delta.T @ activations[layer_i]
                gb = delta.sum(axis=0)
                W, b, name = layers[layer_i]
                W -= LEARNING_RATE * gW
                b -= LEARNING_RATE * gb
                layers[layer_i] = (W, b, name)
                if layer_i > 0:
                    delta = delta @ W


def build_widths_acts(arch: Any) -> tuple[list[int], list[str]]:
    hiddens = _flatten_arch(arch)
    widths = [INPUT_DIM] + [w for _, w in hiddens] + [N_CLASSES]
    acts = [a for a, _ in hiddens] + ["linear"]
    return widths, acts


def n_hidden_units(arch: Any) -> int:
    return int(sum(w for _, w in _flatten_arch(arch)))


def test_accuracy(arch: Any) -> float:
    """Train briefly and return test-set accuracy in ``[0, 1]``."""
    Xtr, ytr, Xte, yte = load_mnist_subset()
    widths, acts = build_widths_acts(arch)
    blob = repr(arch).encode()
    seed = int(hashlib.md5(blob).hexdigest()[:8], 16) % (2**31 - 1)
    rng = np.random.default_rng(seed)
    layers = _init_mlp(widths, acts, rng)
    _train_ce(layers, Xtr, ytr.astype(np.int64), rng)
    logits = _forward(layers, Xte)
    preds = np.argmax(logits, axis=1)
    return float(np.mean(preds == yte.astype(np.int64)))


def error(arch: Any) -> float:
    """Classification error ``1 - accuracy`` on the held-out subset."""
    return float(1.0 - test_accuracy(arch))


def complexity(arch: Any) -> float:
    """Architecture size: total hidden units (minimised as a second objective)."""
    return float(n_hidden_units(arch))


def objectives(arch: Any) -> list[float]:
    """Multi-objective vector ``[error, complexity]`` (one training run)."""
    return [error(arch), complexity(arch)]


def fitness(arch: Any) -> float:
    """Legacy scalar: error + small complexity penalty."""
    err, cx = objectives(arch)
    return float(err + COMPLEXITY_WEIGHT * cx)
