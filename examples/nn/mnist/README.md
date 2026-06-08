# Scalability of exact (SMT) robustness verification — a digits case study

This experiment stress-tests the **relational / exact** verification approach
(`Certify` + z3, see `examples/nn/robustness.ae`) by pointing it at a real
digit classifier and growing the network until it breaks. The question: can
type-level SMT verification reach MNIST-scale?

**Short answer: no — and that is exactly what the literature predicts.** Exact
encodings are complete but exponential; this is why the state of the art
(α,β-CROWN, DeepPoly) uses *linear relaxations* + branch-and-bound instead of
exact SMT.

## Setup

- **Data:** scikit-learn's bundled `digits` (8×8 handwritten digits, 10
  classes) — a genuine digit-recognition task, no download. Input dimension
  is controlled by average-pooling: `downsample 4 → 4` inputs (2×2),
  `2 → 16` (4×4), `1 → 64` (8×8, full).
- **Network:** a fully-connected ReLU MLP (`sklearn.MLPClassifier`), one
  hidden layer of width *H*.
- **Query:** `gen.py` emits an Aeon file encoding the trained network as
  exact `Certify.relu` units and asks z3 to prove **local robustness** around
  one test image — that the true-class logit stays above the runner-up for
  every input in an L∞ ε-ball. Type-checking the file *is* the proof.
- **Harness:** `run_sweep.sh` generates each size, verifies with a wall-clock
  timeout, and records time + verdict in `results.tsv`.

Reproduce:

```bash
bash examples/nn/mnist/run_sweep.sh            # full sweep -> results.tsv
uv run python examples/nn/mnist/gen.py --hidden 8 --downsample 2 --eps 0.02 > q.ae
uv run python -m aeon examples/nn/mnist/verified_small.ae   # a committed robust instance (~4s)
```

## Results (150 s timeout)

| inputs | hidden / ReLUs | time | verdict |
|-------:|---------------:|-----:|---------|
|  4 |  2 |   3 s | not-robust (rejected) |
|  4 |  4 |   5 s | not-robust (rejected) |
|  4 |  8 |  10 s | not-robust (rejected) |
|  4 | 16 |  93 s | not-robust (rejected) |
|  4 | 32 | **timeout (>150 s)** | — |
| 16 |  2 | **timeout (>150 s)** | — |
| 64 |  2 | **timeout (>150 s)** | — |

(`verified_small.ae`: 4 inputs, 4 ReLUs, ε=0.002 → **robust, verified in ~4 s**.)

## What the numbers say

1. **ReLU count is exponential.** At 4 inputs: 8→16→32 ReLUs goes
   10 s → 93 s → timeout — roughly an order of magnitude per doubling. Each
   ReLU is an `if` (an SMT `ite`), so *N* ReLUs encode up to 2^N activation
   patterns. This is the classic complete-verification blow-up.

2. **Input dimension is its own wall.** 16 and 64 inputs time out at *just
   2 ReLUs*, where branching is trivial. z3 is reasoning over a 16- or
   64-dimensional real box with `ite` terms, and the linear-real-arithmetic
   search over many box-constrained variables is already too expensive. So
   the cost is driven by **both** the number of activations **and** the input
   dimensionality — and real images are high-dimensional.

3. **MNIST proper is far out of reach.** Full MNIST is 784 inputs and
   hundreds–thousands of ReLUs. We could not clear *64 inputs with 2 ReLUs*.
   Even the 8×8 digits at full resolution (64 inputs) with a usable hidden
   width is intractable for this exact approach.

## Why this is the expected result

This is precisely the gap the verification field exists to close. Exact SMT
encodings (Reluplex/Marabou, and what we built here) are **sound and
complete** but scale exponentially. The tools that actually verify
MNIST/CIFAR networks give up exactness for **soundness + scalability**:

- **CROWN / DeepPoly** replace each ReLU's exact `ite` with a *linear
  relaxation* (the convex “triangle”), turning the problem into cheap,
  composable bound propagation — polynomial, not exponential.
- **α-CROWN** optimizes the relaxation slopes; **β-CROWN** adds
  branch-and-bound only on the *few* ReLUs that matter, recovering
  completeness without enumerating all 2^N patterns.

Our `Tensor`/`NN` interval measures are the cheap-but-loose end (type-level
IBP); `Certify` is the precise-but-tiny end (exact SMT). The missing middle —
a **relational linear-relaxation layer** (DeepPoly in refinements: bound each
neuron by affine functions of the inputs) — is the principled way to get
useful precision *at scale*, and is the natural next step if this direction
is pursued.

## Files

- `gen.py` — trains the net and emits the Aeon robustness query.
- `run_sweep.sh` — the scaling sweep harness.
- `results.tsv` — raw timing/verdict data from the run above.
- `verified_small.ae` — a committed, reproducible *robust* instance (~4 s).
