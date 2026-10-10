# LiquidHaskell example compatibility

The curated [LiquidHaskell tutorial ports](../examples/liquidhaskell/README.md)
cover arithmetic, inductive datatypes, recursion, measures, FFI trust boundaries,
refinement inference, and diagnostics. They are ordinary `.ae` programs, not
a separate DSL or a Python implementation of the algorithms.

The [manifest](../examples/liquidhaskell/manifest.json) records upstream
files/symbols at a pinned revision, adaptations, expected acceptance/rejection,
and stable/experimental/research status. Positive programs run normally and
with runtime verification. Negatives require the intended compiler error and
source location; native cases distinguish static trust from checked execution.

```bash
uv run pytest tests/liquidhaskell_compatibility_test.py -q
```

This is a regression contract for selected semantic fragments, not Haskell
source compatibility or complete LiquidHaskell parity. The suite README lists
differences and excluded chapters, including monomorphic/specialized ports,
constructor measure invariants, explicit metrics, unreachable branches,
integer semantics, and FFI trust.
