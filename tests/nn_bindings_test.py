"""Tests for the PyTorch-backed NN bindings (optional ``[nn]`` extra).

``aeon/bindings/nn.py`` backs ``libraries/NN.ae``: layers wrap
``torch.nn.Linear``, gradients come from autograd, and shape metadata
(``in_features``/``out_features``) feeds Aeon's refinement types. These tests
pin the numeric semantics the Aeon library relies on; they skip cleanly when
torch is not installed.
"""

from __future__ import annotations

import numpy as np
import pytest

torch = pytest.importorskip("torch")

from aeon.bindings.nn import (  # noqa: E402
    Layer,
    NN_accuracy,
    NN_backward,
    NN_backward_ce,
    NN_build_mlp,
    NN_dense,
    NN_forward,
    NN_grad_in,
    NN_grad_out,
    NN_layer_in,
    NN_layer_out,
    NN_make_layer,
    NN_net_in,
    NN_net_out,
    NN_predict_batch,
    NN_predict_scalar,
    NN_sequential,
    NN_sgd_step,
    NN_softmax_cross_entropy,
    NN_stack,
    NN_train_ce_epochs,
)


def _linear_layer(w, b) -> Layer:
    """Deterministic layer from explicit weights (no random init)."""
    return NN_make_layer(np.asarray(w, dtype=np.float32), np.asarray(b, dtype=np.float32))


# ---------------------------------------------------------------------------
# constructors / shape metadata
# ---------------------------------------------------------------------------


def test_dense_shapes():
    layer = NN_dense(4, 8, "relu")
    assert NN_layer_in(layer) == 4
    assert NN_layer_out(layer) == 8
    assert layer.act == "relu"


def test_make_layer_shapes_and_forward():
    # y = W x + b with W 2x3: exact affine map, no activation.
    layer = _linear_layer([[1, 2, 3], [4, 5, 6]], [0.5, -0.5])
    assert NN_layer_in(layer) == 3
    assert NN_layer_out(layer) == 2
    out = NN_forward(layer, [1.0, 1.0, 1.0])
    np.testing.assert_allclose(out, [6.5, 14.5], rtol=1e-6)


def test_sequential_stack_and_net_widths():
    l1 = _linear_layer([[1, 0], [0, 1], [1, 1]], [0, 0, 0])  # 2 -> 3
    l2 = _linear_layer([[1, 1, 1]], [0])  # 3 -> 1
    net = NN_stack(NN_sequential(l1), l2)
    assert NN_net_in(net) == 2
    assert NN_net_out(net) == 1
    # Stacked prediction composes the affine maps: x=(1,2) -> (1,2,3) -> 6.
    assert NN_predict_scalar(net, [1.0, 2.0]) == pytest.approx(6.0)


def test_build_mlp_widths_and_acts():
    net = NN_build_mlp([4, 8, 8, 3], ["relu", "relu", "linear"])
    assert [(NN_layer_in(ly), NN_layer_out(ly)) for ly in net] == [(4, 8), (8, 8), (8, 3)]
    assert NN_net_in(net) == 4
    assert NN_net_out(net) == 3
    assert [ly.act for ly in net] == ["relu", "relu", "linear"]


# ---------------------------------------------------------------------------
# activations
# ---------------------------------------------------------------------------


def test_relu_clamps_negative_preactivations():
    layer = _linear_layer([[1, 0], [0, 1]], [0, 0])
    layer.act = "relu"
    out = NN_forward(layer, [-3.0, 2.0])
    np.testing.assert_allclose(out, [0.0, 2.0], rtol=1e-6)


@pytest.mark.parametrize(
    "act,expected",
    [
        ("sigmoid", 1.0 / (1.0 + np.exp(-1.0))),
        ("tanh", np.tanh(1.0)),
        ("linear", 1.0),
    ],
)
def test_activation_functions(act, expected):
    layer = _linear_layer([[1.0]], [0.0])
    layer.act = act
    out = NN_forward(layer, [1.0])
    assert out[0] == pytest.approx(expected, rel=1e-6)


# ---------------------------------------------------------------------------
# losses
# ---------------------------------------------------------------------------


def test_softmax_cross_entropy_matches_numpy():
    logits = np.array([2.0, 1.0, 0.1])
    target = np.array([1.0, 0.0, 0.0])
    exp = np.exp(logits - logits.max())
    log_probs = np.log(exp / exp.sum())
    expected = float(-(target * log_probs).sum())
    assert NN_softmax_cross_entropy(logits, target) == pytest.approx(expected, rel=1e-5)


# ---------------------------------------------------------------------------
# autograd gradients
# ---------------------------------------------------------------------------


def test_backward_mse_matches_analytic_gradient():
    # One linear output: loss = (Wx + b - t)^2, so dW = 2(y - t) x^T, db = 2(y - t).
    layer = _linear_layer([[1.0, 2.0]], [0.0])
    net = [layer]
    grads = NN_backward(net, [1.0, 1.0], [1.0])  # y = 3, y - t = 2
    (gW, gb) = grads[0]
    np.testing.assert_allclose(gW, [[4.0, 4.0]], rtol=1e-6)
    np.testing.assert_allclose(gb, [4.0], rtol=1e-6)
    assert NN_grad_in(grads) == 2
    assert NN_grad_out(grads) == 1


def test_backward_ce_gradient_is_softmax_minus_target():
    # Softmax CE from logits of an identity layer: db = softmax(logits) - target.
    layer = _linear_layer([[1.0, 0.0], [0.0, 1.0]], [0.0, 0.0])
    x = np.array([1.0, -1.0])
    target = np.array([1.0, 0.0])
    grads = NN_backward_ce([layer], x, target)
    (_, gb) = grads[0]
    exp = np.exp(x - x.max())
    expected = exp / exp.sum() - target
    np.testing.assert_allclose(gb, expected, rtol=1e-5)


def test_backward_does_not_mutate_input_network():
    layer = _linear_layer([[1.0, 2.0]], [0.5])
    before_w = layer.linear.weight.detach().clone()
    NN_backward([layer], [1.0, 1.0], [0.0])
    assert torch.equal(layer.linear.weight, before_w)
    assert layer.linear.weight.grad is None


def test_sgd_step_applies_gradients_and_returns_new_net():
    layer = _linear_layer([[1.0, 2.0]], [0.5])
    net = [layer]
    grads = [(np.array([[1.0, -1.0]], dtype=np.float32), np.array([2.0], dtype=np.float32))]
    stepped = NN_sgd_step(net, grads, lr=0.1)
    assert stepped is not net and stepped[0] is not layer
    np.testing.assert_allclose(stepped[0].linear.weight.detach().numpy(), [[0.9, 2.1]], rtol=1e-6)
    np.testing.assert_allclose(stepped[0].linear.bias.detach().numpy(), [0.3], rtol=1e-6)
    # The original network is untouched.
    np.testing.assert_allclose(net[0].linear.weight.detach().numpy(), [[1.0, 2.0]], rtol=1e-6)


# ---------------------------------------------------------------------------
# batch helpers
# ---------------------------------------------------------------------------


def test_predict_batch_and_accuracy():
    identity = _linear_layer([[1.0, 0.0], [0.0, 1.0]], [0.0, 0.0])
    net = [identity]
    X = np.array([[3.0, 0.0], [0.0, 5.0], [2.0, 1.0]])
    logits = NN_predict_batch(net, X)
    assert logits.shape == (3, 2)
    np.testing.assert_allclose(logits, X, rtol=1e-6)
    # argmax rows are classes [0, 1, 0]; two of three labels match.
    assert NN_accuracy(net, X, [0, 1, 1]) == pytest.approx(2.0 / 3.0)


def test_accuracy_empty_batch_is_zero():
    net = [_linear_layer([[1.0]], [0.0])]
    assert NN_accuracy(net, np.zeros((0, 1)), np.zeros((0,))) == 0.0


# ---------------------------------------------------------------------------
# end-to-end through libraries/NN.ae
# ---------------------------------------------------------------------------


def test_nn_library_end_to_end():
    """Typecheck and evaluate an Aeon program through libraries/NN.ae: the
    width refinements accept a well-shaped 4 -> 8 -> 3 MLP and the torch-backed
    natives produce a 3-wide probability vector."""
    from aeon.sugar.ast_helpers import st_top

    from tests.driver import check_compile

    src = """
        open Tensor
        open NN

        def main (_: Int) : Int :=
            let l1 := dense_relu 4 8 in
            let l2 := dense 8 3 in
            let net := stack (sequential l1) l2 in
            let probs := softmax (predict net (vzeros 4)) in
            vdim probs;
    """
    assert check_compile(src, st_top, 3)


def test_train_ce_epochs_learns_separable_data():
    torch.manual_seed(0)
    np.random.seed(0)
    # Linearly separable: class = 1 iff x0 > 0.
    X = np.array(
        [[1.0, 0.2], [2.0, -0.3], [1.5, 0.1], [0.8, -0.2], [-1.0, 0.3], [-2.0, -0.1], [-1.5, 0.2], [-0.7, 0.0]]
    )
    y = np.array([1, 1, 1, 1, 0, 0, 0, 0])
    net = NN_build_mlp([2, 8, 2], ["relu", "linear"])
    trained = NN_train_ce_epochs(net, X, y, epochs=60, lr=0.05, batch_size=4)
    assert NN_accuracy(trained, X, y) == 1.0
    # Training returns a new network; the input is unchanged (fresh init is poor).
    assert trained is not net
