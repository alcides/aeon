# DENSER as an Aeon synthesis problem

The search produces an **Aeon expression**, not a Python genome. `mnist.ae`
and `cifar10.ae` each have a single `?architecture` hole whose result must be
a complete, correctly ordered network and learning configuration. The pure
`aeon/libraries/Denser.ae` ADT provides the grammar and checked constructor refinements.
Python only orchestrates Aeon's existing search/compiler and executes tensor
training. There are no axioms about accuracy, shape, or optimizer quality.

The reference is [Genetics_ANN](https://github.com/francescortu/Genetics_ANN/tree/8b4206d60a79e8da51f726a309fa1f4c924a4a90),
particularly its [CNN grammar](https://github.com/francescortu/Genetics_ANN/blob/8b4206d60a79e8da51f726a309fa1f4c924a4a90/src/cnn.grammar.txt),
[training code](https://github.com/francescortu/Genetics_ANN/blob/8b4206d60a79e8da51f726a309fa1f4c924a4a90/scripts/train.py),
and [dataset splits](https://github.com/francescortu/Genetics_ANN/blob/8b4206d60a79e8da51f726a309fa1f4c924a4a90/scripts/dataloader.py).
`provenance.json` pins the source commit, grammar checksum, ranges, and all
intentional differences. This is **not a reproduction of published scores**.

## Building blocks and guarantees

| Block | Choices / checked bounds |
| --- | --- |
| Input | MNIST: 1×28×28; CIFAR-10: 3×32×32; both ten classes |
| Conv | 32–256 filters, kernel 2–5, stride 1–3, same/valid, tanh/relu/sigmoid, Boolean bias |
| Pool | average/max, kernel 2–5, stride 1–3, same/valid |
| Flatten | after 1–10 feature blocks, before classification |
| Dense | 128–2048 units, tanh/relu/sigmoid, Boolean bias; 1–2 blocks |
| Output | fixed dense(10), bias enabled, softmax |
| SGD | lr 0.0001–0.1, momentum 0.68–0.99, decay 0.000001–0.001, nesterov on/off |
| Adam | same lr/decay, beta1/beta2 in [0.5,1) |
| RMSprop | same lr/decay, rho in [0.5,1) |
| Learning | patience 5–20, batch size 50–500, maximum 400 epochs |

Layer phase measures enforce feature → flatten → dense → output → learner.
Feature dimensions have a positive, exact output witness: valid padding needs
kernel ≤ input side; same padding uses ceil(input/stride). Channels are inferred
from the previous block, so callers cannot supply a mismatched input width.
Division by stride is expanded into three constant-divisor cases: these
structural refinements pass `strict_decidable=True`. No nonlinear proof or
uninterpreted shape function is substituted for the actual shape relation.
The Python boundary independently checks witnesses and every grammar range;
it does not repair invalid candidates by dropping layers as upstream does.

Activation codes: 0=tanh, 1=relu, 2=sigmoid. Padding: 0=valid, 1=same.
Pool: 0=average, 1=max. Dataset: 0=MNIST, 1=CIFAR-10.

## Goals

```aeon
@maximize_float(accuracy experiment)
@minimize_int(parameters experiment)
def experiment : {n:Denser | Denser.phase n = 3 && Denser.dataset n = 0} := ?architecture;
```

Accuracy is **measured on held-out validation examples after training** and
lies in [0,1], not an asserted refinement theorem. Parameter count includes
convolution/dense weights, optional biases, and the output head. It excludes
optimizer state and pooling/activation operations, which have no trainable
parameters. Accuracy is upstream's objective; minimizing parameters is an
explicit Aeon extension. Aeon's Pareto search preserves mixed directions
instead of hiding a trade-off in a weighted scalar.

`baseline.ae` is a checked MNIST control with 804,554 parameters. For example:

```aeon
Denser.sgd
  (Denser.softmax (Denser.dense
    (Denser.flatten (Denser.pool
      (Denser.conv (Denser.input 0) 32 3 1 1 1 true 28)
      1 2 2 0 14))
    128 1 true))
  0.01 0.9 0.0001 false 5 50
```

Changing the conv output witness from 28 to 27, placing conv after flatten,
using a 31-filter conv, or learning before the ten-class head is a compile-time
error. The output dimension argument is a proof-checked witness, not a separate
architecture choice with different semantics.

## Running

From the checkout root, install the optional `denser` extra into your venv:

```bash
uv pip install -e '.[denser]'
AEONPATH=examples/synthesis/denser python -m aeon --no-main examples/synthesis/denser/baseline.ae
# Explicit dataset download; omit --download to require already cached data.
python -m aeon.benchmarks.denser --task mnist --prepare /tmp/denser-data --download --data /tmp/denser-mnist.npz
python -m aeon.benchmarks.denser --task mnist --data /tmp/denser-mnist.npz --backend gp --budget 60 --epochs 1
# Increase training cap explicitly for a non-pilot experiment.
python -m aeon.benchmarks.denser --task mnist --data /tmp/denser-mnist.npz --backend gp --budget 3600 --epochs 400
```

For CIFAR-10 change `--task` to `cifar10` and use a separate NPZ. Data preparation
uses only the official **training** dataset: 50k/10k (MNIST), 40k/10k (CIFAR-10),
seed 42, normalization `(image/255 - 0.1307)/0.3081` matching the reference.
The official test set is never consulted during search. An externally supplied
NPZ must contain exactly `X_train`, `y_train`, `X_valid`, `y_valid`; float32 NCHW
images and int64 labels. The caller is responsible for split provenance and
nonoverlap for external archives; array types cannot prove those properties.

`--candidate 'Denser.sgd (...) ...'` evaluates a completed expression instead
of searching. The runner admits only constructor/literal expressions, excluding
self calls, recursors, holes, native bodies, and fitness helpers from the search
space. It checks the whole completed Aeon program before any training.

The runner evaluates fitness directly because real CNN training exceeds the
generic Aeon CLI's ~1s per-candidate worker timeout. The search budget is a soft
wall-clock deadline checked between candidates: compilation and one training
run may overrun it. The 20-million-parameter evaluation cap rejects oversized
networks before allocating weights; it is an operational cap, not an upstream
grammar restriction. This is a large search space: no solution within a short
budget is not a proof of impossibility or a claim that search was exhaustive.

`smoke.ae` deliberately restricts the hole to three activations in a fixed CNN.
`pytest tests/denser_benchmark_test.py` checks real enumerative synthesis and
training on a tiny, explicitly **synthetic** fixture. Torch tests are skipped
when the optional dependency is absent; compiler and property tests still run.
The existing CPU-PyTorch CI job runs these tests with tensor support enabled.
Full grammar architecture optimization and full dataset quality are not inferred
from this bounded smoke test. No dataset is downloaded during CI.

For direct numerical helper calls, `DENSER_DATA=/path/to/archive.npz` and
`DENSER_EPOCHS=1` configure the oracle. Missing data raises an error; no synthetic
or heuristic accuracy silently replaces training.

## Important reference differences

Genetics_ANN's Python initialization does not faithfully execute all its grammar
parameters: feature channels, dense widths and activations are overwritten by
separate random choices; batch normalization is sometimes inserted. Its trainer
always uses fixed SGD, trains a tenth of the data for one epoch during search,
and reports integer-percent accuracy. Here the **grammar** is authoritative:
all three optimizers, all activations, bias, stride and padding choices are
honored, and the full supplied training split is used. Adam beta/rho endpoints
exclude 1 because PyTorch requires that for valid optimizer coefficients.
The grammar's decay field maps to PyTorch `weight_decay`; upstream's trainer
does not interpret that field, so this mapping is not a claim of equivalent
learning-rate scheduling.
Unreachable `amsgrad` and nongrammar adaptive pooling/batch normalization are
not added as extra choices. Same padding supports asymmetric kernels/strides;
average pooling counts explicit zero padding. NLL on softmax probabilities is
used instead of applying cross entropy to already normalized probabilities.
Early stopping returns the best measured validation accuracy within the epoch
cap. These deliberate corrections make this a related synthesis benchmark,
not a bit-for-bit replay of the reference runtime or DENSER's evolutionary engine.
