# Quality gates and compiler sessions

## CI and release validation

The Python application workflow is also the reusable release gate:

- **Lint:** one pre-commit run (including Ruff and mypy), plus strict typing
  of the new compiler phase boundaries. The standalone duplicate Ruff workflow
  has been removed; pre-commit still runs it.
- **Core:** the mandatory fast suite in `scripts/run_core_tests.py`, including
  Hypothesis properties, on Python 3.10–3.14. Failed versions do not cancel the
  other versions.
- **Full suite:** all tests once on Python 3.13 in four isolated worker
  processes with work-stealing to balance slow integration tests. Verbose test
  names make stalled workers diagnosable. No tests are removed from this gate.
- **Trusted-core coverage:** a separate Python 3.13 run of
  `scripts/run_core_tests.py`, reporting compilation, core AST, type-checking
  and verification coverage. This measures the selected core suite, not all
  feature tests. The exhaustive library/synthesis suite with coverage reached
  its 90-minute timeout; separating instrumentation
  keeps exhaustive correctness checks and focused coverage independently visible.
- **Optional backends:** separate OR-Tools and CPU PyTorch jobs. They install
  only their own extras; unavailable accelerators are not claimed as tested.
- **Wheel:** build the wheel from the source distribution, install it into a
  clean environment, then verify packaged grammars, standard-library imports,
  and execution in an isolated process outside the checkout.
- **Examples:** every `.ae` file under `examples/` is discovered recursively
  and assigned to exactly one of eight deterministic shards on Python 3.13.
  Each shard uses two isolated CLI workers, with a 120-second per-file timeout.
  `--check --no-main` parses, elaborates and verifies refinements, allowing
  synthesis holes without running synthesis, fitness functions,
  LLVM compilation or program evaluation. This includes nested benchmark
  corpora such as MBPP, SRBench, DACE, Karel and SyGuS.
  The existing `examples/testing/` suites and `props_*`/`examples_*` PBT examples
  still execute with `--test --seed 0`. Negative cases in the typestate and
  LiquidHaskell manifests must produce a refinement/type diagnostic, not a
  syntax error, missing import, crash or synthesis timeout. Shards continue
  independently after failures and retain per-file logs and JSON timing/results.
  The intentionally unresolved monotonicity proof specifications must reject
  their missing implementations, then prove completed reference controls through
  the existing benchmark validator (`--candidate`, never synthesis search).
  An aggregate `examples` check retains the original branch-protection check
  name and succeeds only when every shard succeeds.
- **Research:** scheduled/manual runs use a larger Hypothesis campaign and
  benchmark regression tests, retaining JUnit timings. These are regression
  checks, not claims of reproducing published synthesis results.
  `scripts/benchmark_compilation.py` also records independent-session compile
  timings, source hashes, and environment metadata; disk caches may be present,
  and the measurements are not synthesis timings or an absolute speed gate.

JUnit and trusted-core coverage reports are retained as workflow artifacts.
Releases publish the exact wheel and source distribution produced by the wheel
gate, rather than rebuilding after tests. Publishing still requires a version
tag and the existing PyPI token. Branch protection settings must be updated
separately if they require the old `build (version)` or standalone Ruff job names.

The selected core suite is deliberately small; the full-suite job remains
required to cover features outside that cross-version gate. The existing policy
for stochastic synthesis skips is unchanged by this CI refactor.

Run the expanded example gate locally (or inspect its coverage without running):

```bash
bash run_examples.sh --jobs 2
bash run_examples.sh --list
bash run_examples.sh --shard 0 --shards 8
bash run_examples.sh --failures-from example-results/results.json
uv run python -m aeon --check examples/synthesis/dace/pbe/col_offset.ae
```

Example checking is not a claim that benchmark holes are solvable, that opaque
native implementations are correct, or that accelerator/remote services work.
The compiler's normal compile-time evaluation of closed refinement expressions
still applies; `--check` suppresses runtime execution, not refinement verification.

PSB2 multi-objective examples use one objective per training case (200, or 50
for `leaders`), rather than confusing output-vector arity with objective count.
Their native objective-vector conversion checks the actual length before
returning its refined array. Single-objective array getters are functions so
that every invocation produces a fresh linear array.

## Compilation sessions

`CompilationSession` owns lazily constructed, typed state for:

- compiled source units and module units;
- parsed imports and cycle guards;
- typeclass instances and inductive constructors/measures;
- the solver, validity/PLE/translation caches, and SMT datatype caches;
- compilation options and diagnostics.

Use an explicit session when several low-level operations must share state:

```python
from aeon.compilation.compile import compile_file
from aeon.compilation.session import CompilationOptions, CompilationSession

session = CompilationSession(CompilationOptions(smt_timeout_ms=500, cache_limit=1024))
with session.activate():
    unit, errors = compile_file("Library.ae", write_cache=False)
```

Top-level compilation entrypoints create a fresh session unless one is already
active; recursive imports share the active session. `AeonDriver` retains its
session for execution, export, property testing, and synthesis, and creates a new
session for each parse. Nested activation restores the previous owner even after
exceptions. Standalone low-level registry APIs retain context-local compatibility
state, but that state is not reused by independent compilation entrypoints.

Sessions are not a promise of thread-safe Z3 execution: do not share one session
across concurrent threads. Process-wide binder IDs and Z3 measure declaration
IDs remain unique identity allocators, not caches of program semantics. On-disk
cache serialization and dependency-fingerprint validation are separate concerns;
this refactor does not change their trust policy.

Module-interface construction now lives in `aeon.compilation.interface`, name
resolution in `aeon.sugar.name_resolution`, and solver state in
`aeon.verification.state`. Existing desugaring imports remain compatible.
Core substitution recursion reuses these functions' typed boundaries instead of
creating annotated local helpers repeatedly under runtime instrumentation.
Liquid substitution also uses a fresh memo per call to retain shared refinement
subterms. This avoids expanding a small expression DAG into an exponential
tree, without caching results across replacements or compiler sessions.

## Hypothesis invariants

The generated suite checks beta-substitution/evaluation, free-variable
accounting, capture avoidance in type substitution, alpha-renaming of programs
and refinement proofs, cached versus uncached unit interfaces and
values, interpreter/Python-export/LLVM agreement, and independent type checking
of deterministic synthesized candidates. Arithmetic backend comparisons use
bounded integer expressions in the shared backend subset, not floating-point,
overflow, native, or GPU behavior. Failed examples are shrunk by Hypothesis.

Run the same fast gate locally:

```bash
HYPOTHESIS_PROFILE=ci uv run --extra tests python scripts/run_core_tests.py -q
HYPOTHESIS_PROFILE=nightly uv run --extra tests pytest tests/core_properties_test.py -q
```

The CI profile uses 40 deterministic examples per property and no wall-clock
deadline; the nightly profile uses 200 examples and Hypothesis's normal example
database. The default local profile is unchanged. See the
[Hypothesis settings reference](https://hypothesis.readthedocs.io/en/latest/reference/api.html#settings)
for reproduction and configuration. Coverage is reported without an arbitrary
percentage gate; changes should add tests for the affected verification paths.
