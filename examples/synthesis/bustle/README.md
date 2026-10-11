# BUSTLE synthesis

`-s bustle` implements the main loop of Odena et al.,
[BUSTLE: Bottom-Up Program Synthesis Through Learning-Guided Exploration](https://arxiv.org/abs/2007.14381)
(ICLR 2021), following Algorithm 1 and the
[zaxtax/bustle implementation](https://github.com/zaxtax/bustle).

```bash
python -m aeon --no-main --budget 10 -s bustle examples/synthesis/bustle/string.ae
python -m aeon --no-main --budget 10 -s bustle examples/synthesis/bustle/add.ae
python -m aeon --no-main --budget 10 -s bustle examples/synthesis/bustle/list.ae
python -m aeon --no-main --budget 10 -s bustle examples/synthesis/bustle/tree.ae
# The same search without the trained model, for comparison:
python -m aeon --no-main --budget 10 -s bustle_baseline examples/synthesis/bustle/string.ae
```

Declare scalar or closed-constructor `@example(f args = result)` assertions and an expression hole
inside `f`. Library functions in scope supply the DSL. For example, `string.ae`
offers separate trimming and uppercase primitives and asks Aeon to compose them;
one solution is `trim (upper text)`.

## Algorithm

1. Seed weight 1 with inputs, in-scope scalar/ADT constants, the paper's small integer
   literals, delimiters occurring in the examples, and repeated string substrings.
2. Enumerate typed applications bottom-up: an operator contributes 1, and its
   children contribute their **adjusted** weights.
3. Evaluate an expression on every example, retaining one representative for
   each `(type, output vector)` rather than every syntax tree. ADT observations
   retain the complete constructor tree and typed scalar payloads; root tag and
   depth alone never define equivalence. Runtime errors
   and values outside the scalar/structural bounds are discarded.
4. Compute property signatures of input/output and intermediate/output pairs.
   A property is `AllFalse = -1`, `Mixed = 0`, or `AllTrue = 1`. Non-applicable
   types and padded input slots use a distinct value, 2. ADT properties include
   nullary constructors, depth/size thresholds, structural identity, shared root
   constructor, relative depth/size, and subtree relationships. Constructor
   identity means a stable constructor tag, not Python object identity.
5. Batch predictions from a trained two-hidden-layer MLP. Discretize usefulness
   probability at 0.1, 0.2, 0.3, 0.4, and 0.6, as in paper §3.2, then store the
   intermediate expression at `weight + 5 - bin`. Unlikely subexpressions are
   delayed, not removed. Initial inputs and constants stay at weight 1.
6. Return an example-consistent expression only after Aeon's validation oracle
   accepts it against its full type. Matching examples alone is insufficient.

The signature schema is version 2; older scalar-only checkpoints are rejected
as incompatible. A model checkpoint is bundled in the installed package. Inference uses NumPy
when available and otherwise uses the same weights with standard-library
arithmetic; installing PyTorch, scikit-learn, or downloading a model is not
required. An invalid or missing configured checkpoint causes a clear error,
rather than silently switching to the unguided algorithm. Set
`AEON_BUSTLE_MODEL=/path/to/model.json` to use a separately trained checkpoint.

## Reproducing training

The training generator follows paper §3.1: run unguided searches over synthetic
scalar, list, and binary-tree inputs, sample target expressions from their value banks, sample proper
subexpressions as positive examples, and sample non-subexpressions of the same
type as negatives. It excludes observationally equivalent positives from the
negative pool. No human benchmark examples are used to train the bundled model.
Validation holds out entire searches, including all their sampled targets.

With NumPy installed (included by Aeon's optional `ml`/`dev` extras):

```bash
OPENBLAS_NUM_THREADS=1 python -m aeon.synthesis.modules.bustle.train \
    --searches 200 --epochs 40 --seed 0 --output /tmp/bustle-model.json
AEON_BUSTLE_MODEL=/tmp/bustle-model.json python -m aeon --no-main --budget 10 \
    -s bustle examples/synthesis/bustle/string.ae
```

The bundled checkpoint records its seed, generator version, row counts, and
metrics. It was trained on 12,126 rows from 160 searches and validated on 3,038
rows from 40 other searches. Binary cross-entropy fell from 0.708 to 0.297;
validation classification accuracy was 84.4%. These measure the synthetic
usefulness classifier, **not** benchmark solve rate or synthesis speedup.
Floating-point differences between NumPy versions/platforms may change weights
slightly when retraining.

## Scope and differences from the paper

This is an Aeon adaptation, not a reproduction of the paper's reported
performance or its full spreadsheet DSL. It supports one to three scalar or ADT
parameters, scalar or registered ADT results, concrete first-order library components (up to
three arguments), prelude operators instantiated at supported types,
and conditionals. Input order is preserved in three fixed signature slots.
Monomorphic ADTs and concrete instantiations of polymorphic ADTs are supported,
including polymorphic nullary constructors. Constructors and first-order helper
functions supply the DSL; this does not generate recursive functions or match
handlers. Constructor-valued examples use closed constructor syntax. Their
metadata is separate from Contata's legacy flattened list encoding.
The property list extends a compact string/numeric/boolean subset with ADT
structural predicates; unlike the paper's
embedded trits, the MLP consumes numeric signatures directly. It uses 32/16
hidden units and a portable JSON checkpoint instead of the reference repository's
PyTorch checkpoint. Training uses a smaller synthetic search corpus.

No generated recursion, higher-order components, Float values, opaque pipeline/model
objects, additional optimization objectives, or relational/non-literal example
assertions are supported. Adding ADT support does not add fitness optimization. Aeon's numeric CSV decorators currently produce
Float examples and fall outside this DSL. This backend synthesizes scalar/ADT
functions from examples; it does not directly solve the `examples/ml/amltk_*`
opaque-model optimization benchmarks.

Search stops at the time budget, adjusted weight 40, or 20,000 distinct value
vectors. Strings are bounded to 256 characters and integers to absolute value
10^9. ADTs are bounded to depth 16 and 128 constructor nodes. Every node must
match a registered constructor and its instantiated field types; unregistered
tagged native tuples and malformed payloads are rejected. These limits also keep constant extraction and property evaluation small.
Native primitive execution and final type validation can extend a search step
past its deadline. Expressions failing on any example are discarded, including
otherwise usable partial branches of a conditional, matching the linked
repository's error-handling policy.

Observational equivalence is relative to the examples, not all possible inputs.
Aeon still checks the final expression's type. A different matching
representative is checked even if its value vector was already seen, but
retaining just one intermediate representative can reduce completeness when
refinement contracts distinguish two otherwise example-equivalent expressions.
