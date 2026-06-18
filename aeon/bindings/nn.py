"""Python bindings for the Aeon ``NN`` library — forward/backward passes.

A ``Layer`` is the tuple ``(W, b, act)`` with ``W`` of shape
``(out_features, in_features)``, ``b`` of shape ``(out_features,)`` and
``act`` one of ``"linear" | "relu" | "sigmoid" | "tanh"``. A ``Network``
is a Python list of layers.

``Gradients`` mirrors a network's structure: a list ``[(gW, gb), ...]``
where ``gW``/``gb`` have the same shapes as the corresponding layer's
``W``/``b``. Two losses are supported:

* ``NN_backward`` — mean-squared-error ``L = mean((output - target) ** 2)``,
  with the network output taken as-is (use a ``linear`` final layer for
  regression).
* ``NN_backward_ce`` — softmax cross-entropy, treating the network output
  as logits. Because ``dL/d(output) = softmax(output) - target`` for this
  loss, the only thing that differs from the MSE case is the seed gradient
  at the output; the rest of backprop is shared via ``_backprop``.

The shape contracts the Aeon types rely on — ``grad_in`` / ``grad_out``
matching ``net_in`` / ``net_out`` — hold because each ``gW`` matches its
layer's ``W``. Functions are named ``NN_<name>`` and called positionally
from the native strings in ``libraries/NN.ae``.
"""

from __future__ import annotations

from typing import Any

import numpy as np

_ACTIVATIONS = {
    "linear": lambda z: z,
    "relu": lambda z: np.maximum(z, 0.0),
    "sigmoid": lambda z: 1.0 / (1.0 + np.exp(-z)),
    "tanh": lambda z: np.tanh(z),
}


def _activation_deriv(name: str, z: Any, a: Any) -> Any:
    """Derivative of the activation w.r.t. its pre-activation ``z``.

    ``a`` is the already-computed post-activation, used where it makes the
    derivative cheaper (sigmoid, tanh).
    """
    if name == "relu":
        return (z > 0.0).astype(float)
    if name == "sigmoid":
        return a * (1.0 - a)
    if name == "tanh":
        return 1.0 - a * a
    return np.ones_like(z)  # linear


def _stable_softmax(z: Any) -> Any:
    """Numerically stable softmax of a 1-D logit vector."""
    e = np.exp(z - np.max(z))
    return e / np.sum(e)


def _forward_cache(net, x):
    """Forward pass returning per-layer pre-activations and activations.

    ``activations[l]`` is the input fed to layer ``l`` (``activations[0]``
    is ``x``); ``pre[l]`` is ``(z, act_name)`` for layer ``l``.
    """
    a = np.asarray(x, dtype=float)
    activations = [a]
    pre = []
    for W, b, name in net:
        z = W @ a + b
        a = _ACTIVATIONS[name](z)
        pre.append((z, name))
        activations.append(a)
    return activations, pre


def _backprop(net, activations, pre, dloss_doutput):
    """Backpropagate a seed gradient ``dL/d(output)`` into per-layer grads.

    ``dloss_doutput`` is the gradient of the loss w.r.t. the network's
    final activation. Returns ``[(gW, gb), ...]`` parallel to ``net``.
    """
    delta = dloss_doutput
    grads: list = [None] * len(net)
    for layer in range(len(net) - 1, -1, -1):
        z, name = pre[layer]
        delta = delta * _activation_deriv(name, z, activations[layer + 1])
        gW = np.outer(delta, activations[layer])
        gb = delta
        grads[layer] = (gW, gb)
        if layer > 0:
            W = net[layer][0]
            delta = W.T @ delta
    return grads


def NN_backward(net, x, target):
    """Gradients of the MSE loss w.r.t. every layer's weights and bias."""
    activations, pre = _forward_cache(net, x)
    out = activations[-1]
    target = np.asarray(target, dtype=float)
    n = out.shape[0]
    # dL/d(output) for L = mean((output - target) ** 2).
    seed = (2.0 / n) * (out - target)
    return _backprop(net, activations, pre, seed)


def NN_backward_ce(net, x, target):
    """Gradients of the softmax cross-entropy loss.

    The network output is read as logits; the seed gradient simplifies to
    ``softmax(logits) - target``, which is correct for any architecture
    (for a ``linear`` final layer this is the textbook ``p - target``).
    """
    activations, pre = _forward_cache(net, x)
    out = activations[-1]
    target = np.asarray(target, dtype=float)
    # dL/d(output) for L = -sum(target * log(softmax(output))).
    seed = _stable_softmax(out) - target
    return _backprop(net, activations, pre, seed)


def NN_softmax_cross_entropy(logits, target):
    """Numerically stable softmax cross-entropy from logits (non-negative)."""
    z = np.asarray(logits, dtype=float)
    z = z - np.max(z)
    log_probs = z - np.log(np.sum(np.exp(z)))
    return float(-np.sum(np.asarray(target, dtype=float) * log_probs))


def NN_sgd_step(net, grads, lr):
    """Return a new network with one gradient-descent step applied.

    ``W <- W - lr * gW`` and ``b <- b - lr * gb`` for every layer. Shapes
    (and therefore ``net_in`` / ``net_out``) are preserved.
    """
    return [(W - lr * gW, b - lr * gb, name) for (W, b, name), (gW, gb) in zip(net, grads)]
