"""Python bindings for the Aeon ``NN`` library — PyTorch-backed.

A ``Layer`` is a thin wrapper around ``torch.nn.Linear`` plus an activation
tag (``"linear" | "relu" | "sigmoid" | "tanh"``). A ``Network`` is a Python
list of layers. ``Gradients`` mirrors a network: ``[(gW, gb), ...]`` where
each ``gW`` / ``gb`` is a NumPy array matching the corresponding layer's
weight / bias shapes (so Aeon's ``Tensor`` refinements stay NumPy-native).

Forward and loss use PyTorch; ``NN_backward`` / ``NN_backward_ce`` obtain
gradients via ``torch.autograd`` rather than a hand-rolled backprop. The
shape contracts Aeon relies on — ``grad_in`` / ``grad_out`` matching
``net_in`` / ``net_out`` — hold because each ``gW`` matches its layer's
``weight``.

Functions are named ``NN_<name>`` and called from the native strings in
``libraries/NN.ae``.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from typing import Any, Literal

import numpy as np

try:
    import torch
    import torch.nn as nn
    import torch.nn.functional as F
except ImportError as exc:  # pragma: no cover - exercised when torch missing
    raise ImportError(
        "The Aeon NN library requires PyTorch. Install it with: "
        'uv pip install "AeonLang[nn]"   or   uv pip install torch'
    ) from exc

ActName = Literal["linear", "relu", "sigmoid", "tanh"]


@dataclass
class Layer:
    """One affine map ``x |-> act(W x + b)`` backed by ``torch.nn.Linear``."""

    linear: nn.Linear
    act: ActName

    @property
    def in_features(self) -> int:
        return int(self.linear.in_features)

    @property
    def out_features(self) -> int:
        return int(self.linear.out_features)


def _as_float_tensor(x: Any) -> torch.Tensor:
    if isinstance(x, torch.Tensor):
        return x.detach().to(dtype=torch.float32)
    return torch.as_tensor(np.asarray(x, dtype=np.float32), dtype=torch.float32)


def _activate(z: torch.Tensor, act: ActName) -> torch.Tensor:
    if act == "relu":
        return F.relu(z)
    if act == "sigmoid":
        return torch.sigmoid(z)
    if act == "tanh":
        return torch.tanh(z)
    return z


def _apply_layer(layer: Layer, x: torch.Tensor) -> torch.Tensor:
    return _activate(layer.linear(x), layer.act)


def _forward_tensor(net: list[Layer], x: torch.Tensor) -> torch.Tensor:
    out = x
    for layer in net:
        out = _apply_layer(layer, out)
    return out


def _clone_net(net: list[Layer]) -> list[Layer]:
    return [Layer(linear=deepcopy(layer.linear), act=layer.act) for layer in net]


def _make_dense(nin: int, nout: int, act: ActName) -> Layer:
    linear = nn.Linear(nin, nout)
    # Match the previous NumPy ``* 0.1`` scale so existing tiny demos still train.
    nn.init.normal_(linear.weight, mean=0.0, std=0.1)
    nn.init.zeros_(linear.bias)
    return Layer(linear=linear, act=act)


# ─── constructors / inspection ───────────────────────────────────────────


def NN_dense(nin: int, nout: int, act: str = "linear") -> Layer:
    return _make_dense(int(nin), int(nout), act)  # type: ignore[arg-type]


def NN_make_layer(w: Any, b: Any) -> Layer:
    """Build a linear layer from NumPy weight ``(out, in)`` and bias ``(out,)``."""
    W = np.asarray(w, dtype=np.float32)
    bias = np.asarray(b, dtype=np.float32)
    nout, nin = W.shape
    linear = nn.Linear(nin, nout)
    with torch.no_grad():
        linear.weight.copy_(torch.as_tensor(W))
        linear.bias.copy_(torch.as_tensor(bias))
    return Layer(linear=linear, act="linear")


def NN_layer_in(layer: Layer) -> int:
    return layer.in_features


def NN_layer_out(layer: Layer) -> int:
    return layer.out_features


def NN_sequential(layer: Layer) -> list[Layer]:
    return [layer]


def NN_stack(net: list[Layer], layer: Layer) -> list[Layer]:
    return list(net) + [layer]


def NN_net_in(net: list[Layer]) -> int:
    return net[0].in_features


def NN_net_out(net: list[Layer]) -> int:
    return net[-1].out_features


# ─── forward ─────────────────────────────────────────────────────────────


def NN_forward(layer: Layer, x: Any) -> np.ndarray:
    with torch.no_grad():
        out = _apply_layer(layer, _as_float_tensor(x))
    return out.detach().cpu().numpy().astype(float)


def NN_predict(net: list[Layer], x: Any) -> np.ndarray:
    with torch.no_grad():
        out = _forward_tensor(net, _as_float_tensor(x))
    return out.detach().cpu().numpy().astype(float)


def NN_predict_scalar(net: list[Layer], x: Any) -> float:
    return float(NN_predict(net, x)[0])


# ─── losses ──────────────────────────────────────────────────────────────


def NN_softmax_cross_entropy(logits: Any, target: Any) -> float:
    z = _as_float_tensor(logits)
    t = _as_float_tensor(target)
    log_probs = F.log_softmax(z, dim=0)
    return float(-(t * log_probs).sum().item())


# ─── backprop via autograd ───────────────────────────────────────────────


def _grads_from_loss(net: list[Layer], x: Any, target: Any, kind: str) -> list[tuple[np.ndarray, np.ndarray]]:
    # Clone so training demos that share a network handle stay isolated from
    # autograd graph mutation of the live parameters.
    work = _clone_net(net)
    for layer in work:
        layer.linear.weight.requires_grad_(True)
        layer.linear.bias.requires_grad_(True)

    pred = _forward_tensor(work, _as_float_tensor(x))
    tgt = _as_float_tensor(target)
    if kind == "mse":
        loss = torch.mean((pred - tgt) ** 2)
    else:
        # Softmax CE from logits: seed is softmax(pred) - target.
        log_probs = F.log_softmax(pred, dim=0)
        loss = -(tgt * log_probs).sum()
    loss.backward()

    grads: list[tuple[np.ndarray, np.ndarray]] = []
    for layer in work:
        assert layer.linear.weight.grad is not None
        assert layer.linear.bias.grad is not None
        grads.append(
            (
                layer.linear.weight.grad.detach().cpu().numpy().astype(float),
                layer.linear.bias.grad.detach().cpu().numpy().astype(float),
            )
        )
    return grads


def NN_backward(net: list[Layer], x: Any, target: Any) -> list[tuple[np.ndarray, np.ndarray]]:
    """Gradients of the MSE loss w.r.t. every layer's weights and bias."""
    return _grads_from_loss(net, x, target, "mse")


def NN_backward_ce(net: list[Layer], x: Any, target: Any) -> list[tuple[np.ndarray, np.ndarray]]:
    """Gradients of softmax cross-entropy (network output read as logits)."""
    return _grads_from_loss(net, x, target, "ce")


def NN_grad_in(grads: list[tuple[np.ndarray, np.ndarray]]) -> int:
    return int(grads[0][0].shape[1])


def NN_grad_out(grads: list[tuple[np.ndarray, np.ndarray]]) -> int:
    return int(grads[-1][0].shape[0])


def NN_sgd_step(net: list[Layer], grads: list[tuple[np.ndarray, np.ndarray]], lr: float) -> list[Layer]:
    """Return a new network with one gradient-descent step applied."""
    out = _clone_net(net)
    with torch.no_grad():
        for layer, (gW, gb) in zip(out, grads):
            layer.linear.weight -= float(lr) * torch.as_tensor(gW, dtype=torch.float32)
            layer.linear.bias -= float(lr) * torch.as_tensor(gb, dtype=torch.float32)
    return out


# ─── batch helpers (MNIST / neuroevolution) ──────────────────────────────


def NN_predict_batch(net: list[Layer], X: Any) -> np.ndarray:
    """Forward a batch ``(n, features)``; returns ``(n, classes)`` logits."""
    with torch.no_grad():
        out = _forward_tensor(net, _as_float_tensor(X))
    return out.detach().cpu().numpy().astype(float)


def NN_accuracy(net: list[Layer], X: Any, y: Any) -> float:
    """Fraction of correctly classified rows (``y`` are integer class ids)."""
    logits = NN_predict_batch(net, X)
    preds = np.argmax(logits, axis=1)
    labels = np.asarray(y).astype(int).ravel()
    if labels.size == 0:
        return 0.0
    return float(np.mean(preds == labels))


def NN_train_ce_epochs(
    net: list[Layer],
    X: Any,
    y: Any,
    epochs: int,
    lr: float,
    batch_size: int = 64,
) -> list[Layer]:
    """Train ``net`` with Adam + softmax CE for ``epochs`` mini-batch passes.

    ``y`` is a vector of integer class labels. Returns a fresh network.
    """
    work = _clone_net(net)
    params = []
    for layer in work:
        params.extend(layer.linear.parameters())
    opt = torch.optim.Adam(params, lr=float(lr))

    X_t = _as_float_tensor(X)
    y_t = torch.as_tensor(np.asarray(y).astype(np.int64).ravel(), dtype=torch.long)
    n = int(X_t.shape[0])
    bs = max(1, int(batch_size))
    epochs_i = max(0, int(epochs))

    for _ in range(epochs_i):
        perm = torch.randperm(n)
        for start in range(0, n, bs):
            idx = perm[start : start + bs]
            xb = X_t[idx]
            yb = y_t[idx]
            opt.zero_grad()
            logits = _forward_tensor(work, xb)
            loss = F.cross_entropy(logits, yb)
            loss.backward()
            opt.step()
    return work


def NN_build_mlp(widths: list[int], acts: list[str]) -> list[Layer]:
    """Build an MLP from layer widths ``[in, h1, ..., out]`` and per-layer acts.

    ``len(acts) == len(widths) - 1``. The final act is typically ``"linear"``
    (logits) for classification.
    """
    assert len(widths) >= 2
    assert len(acts) == len(widths) - 1
    layers: list[Layer] = []
    for i in range(len(acts)):
        layers.append(_make_dense(int(widths[i]), int(widths[i + 1]), acts[i]))  # type: ignore[arg-type]
    return layers
