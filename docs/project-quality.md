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
  processes with work-stealing to balance slow integration tests, and coverage reports for
  compilation, core ASTs, type checking, and verification.
- **Optional backends:** separate OR-Tools and CPU PyTorch jobs. They install
  only their own extras; unavailable accelerators are not claimed as tested.
- **Wheel:** build the wheel from the source distribution, install it into a
  clean environment, then verify packaged grammars, standard-library imports,
  and execution in an isolated process outside the checkout.
- **Examples:** the existing example suite runs once, rather than once per
  Python version.
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
