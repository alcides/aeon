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

## Follow-up: a linear-relaxation prototype (DeepPoly-in-refinements)

`relax_gen.py` + `libraries/Relax.ae` sketch the principled fix: replace each
unstable ReLU's exact `(y == 0 || y == x)` with its convex **triangle
relaxation** (`y >= 0`, `y >= z`, `y <= a*z + b`) — sound linear bounds with
**no disjunction**, so the solver never case-splits. Stable neurons stay
exact; the per-neuron pre-activation interval `[l, u]` is exact for one
hidden layer (affine over the box). See `examples/nn/relaxation.ae` for the
idea on a hand-written net.

**Does it unlock scale? Not on its own.** Controlled, same-machine,
back-to-back (4 inputs, 6 unstable ReLUs):

| width | exact (Certify) | relaxed (Relax) |
|------:|----------------:|----------------:|
|  8 |  9 s |  8 s |
| 16 | 94 s | 71 s |

Removing the case-splitting helps only modestly (~25%), and **both blow up
with network width**. Even a *purely affine* relaxed net (0 unstable ReLUs)
goes 9 s → 74 s from width 8 → 16. So in this refinement-typed encoding the
dominant cost is **not** ReLU case-splitting — it is the size of the
verification condition, which grows steeply with width because every neuron
is inlined as an affine expression over the inputs and chained through
`let`s. (Numbers are on a loaded machine, so absolute values are inflated;
the *ratios*, measured back-to-back, are the signal.)

**Takeaway.** The relaxation is necessary (it's the only way to avoid the
exponential ReLU split) but **not sufficient**. To actually scale, it must be
paired with a leaner encoding that keeps the VC linear in network size —
e.g. introducing each neuron as an *opaque* SMT variable constrained by its
(relaxed) bounds, rather than inlining its defining expression everywhere it
is used. That VC-engineering step, plus multi-layer DeepPoly
back-substitution to keep the `[l, u]` tight, is the real road to scale.

## Chasing the bottleneck: "make it opaque so it scales"

The natural next hypothesis was that the relaxed encoding stalls because each
neuron is *inlined* (its defining expression copied everywhere it is used),
and that representing neurons as opaque SMT variables would fix it. Profiling
(`python -m cProfile -m aeon q.ae`) on a width-10 relaxed query showed two
things:

1. **Aeon already makes neurons opaque.** The verification condition is
   literally `∀h0. h0 == <affine> → ∀h1. h1 == <affine> → ... → margin > 0`:
   each `let` is lowered to a fresh quantified variable plus one defining
   equation. Opacity was not the missing piece.

2. **The cost is in the SMT *translation*, not z3's search and not ReLU
   case-splitting.** `aeon/verification/smt.py:translate_liq` accounted for
   ~22 s of a 38 s run and was called **~405,000 times** for a ~10-equation
   problem. It is a *non-memoized* recursive descent, and the nested
   `∀h. h==e → ...` chain makes it re-translate overlapping sub-formulas over
   and over — cost grows with the verification-condition size = (number of
   bindings) × (terms per affine).

So the lever is to **shrink the VC**, not to add opacity. `relax_flat_gen.py`
does this: for a single hidden layer the network is piecewise affine, so every
*stable* ReLU (interval entirely ≥0 or ≤0) folds exactly into one collapsed
affine form, and only the *unstable* ReLUs remain as bindings. Binding depth
becomes `#unstable`, not width.

Deterministic, load-independent evidence (same net, 4 inputs, 8 hidden,
4 unstable — `translate_liq` call counts don't depend on machine load):

| encoding | bindings | `translate_liq` calls |
|----------|---------:|----------------------:|
| `relax_gen.py` (per-neuron) | 8 | 161,018 |
| `relax_flat_gen.py` (folded) | 4 | 97,656 |

The translation work drops in step with the bindings removed; at width 32 the
fold is 32 → ~4, a much larger cut.

**Honest bottom line.** Folding is the right encoding-level lever and it helps
proportionally, but it does *not* by itself reach MNIST scale: the input
dimension (terms per affine — 64 for a full 8×8 image) and the high per-term
constant of the non-memoized translator remain. The decisive fix is in Aeon
core — **memoize `translate_liq` / share z3 sub-expressions** so the VC is
translated once instead of re-walked per clause. That is an interpreter
change, outside this library; the relaxation + folding here are what the
library layer can soundly contribute. (Timings on this machine were too
load-contaminated to report as a scaling curve; the call-count comparison
above is deterministic and is the reliable signal.)

## Files

- `gen.py` — trains the net and emits the *exact* Aeon robustness query.
- `relax_gen.py` — *linear-relaxation* (DeepPoly-style), one binding per neuron.
- `relax_flat_gen.py` — relaxation **+ stable-neuron folding** (binding depth = #unstable).
- `run_sweep.sh` — the scaling sweep harness.
- `results.tsv` — raw timing/verdict data from the exact sweep above.
- `verified_small.ae` — a committed, reproducible *robust* instance (~4 s).
