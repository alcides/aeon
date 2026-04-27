# Aeon Development FAQ

This is a list of questions (and responses) that may come up while developing for the first time on **Aeon**.

---

## How to install?

### Requirements:

- [Uv](https://github.com/astral-sh/uv)
- [Pre-Commit](https://pre-commit.com/)

### Installation:

After cloning the project, run:
  * `uv pip install -e ".[dev]"`
  * `uvx pre-commit install`

### Running the project and tests

- To run a .ae file: `uv run python -m aeon [flags] [file]`
- To run the tests: `uv run pytest`
- To run a single test: `uv run pytest tests/end_to_end_test.py::test_name -x`
- To run all examples (used in CI): `bash run_examples.sh`

---

## Pre-commit

This project uses [pre-commit](https://pre-commit.com/) hooks to enforce code quality on every commit. After installing with `uvx pre-commit install`, the following hooks run automatically:

- **pre-commit-hooks**: YAML/TOML validation, merge conflict detection, trailing whitespace, end-of-file fixer, docstring-first check, mixed line endings
- **setup-cfg-fmt**: Formats `setup.cfg`
- **mypy**: Static type checking (with `--no-strict-optional`, `--ignore-missing-imports`, `--explicit-package-bases`)
- **ruff**: Linting (with `--fix`) and formatting
- **pyroma**: Package metadata validation

To run all hooks manually: `uvx pre-commit run --all-files`

---

## Architecture of the compiler

Aeon follows a classic compiler pipeline:

```
Source (.ae) --> Parse (lark) --> Sugar AST --> Desugar/Elaborate --> Core AST --> ANF --> Typecheck (z3 SMT) --> Synthesize/Evaluate
```

### Key packages

| Package | Role |
|---|---|
| `aeon/facade` | Entry point: `AeonDriver` orchestrates the full pipeline, `AeonConfig` holds settings |
| `aeon/sugar` | Surface language: AST (`STypes`/`STerm` in `program.py`), parser (lark grammar in `aeon_sugar.lark`), desugaring |
| `aeon/core` | Core language: `Types`/`Term` (internal representation, never user-facing), substitutions, liquid constraints, core term/type parser |
| `aeon/frontend` | ANF conversion |
| `aeon/elaboration` | Converts sugar AST to core AST with type elaboration |
| `aeon/typechecking` | Type inference and liquid type constraint verification |
| `aeon/verification` | SMT-based verification via z3: horn clauses, constraint solving |
| `aeon/synthesis` | Program synthesis: multiple backends (genetic programming via geneticengine, synquid, enumerative, LLM/ollama) |
| `aeon/backend` | Runtime evaluation |
| `aeon/lsp` | Language Server Protocol implementation (pygls) |
| `aeon/prelude` | Built-in functions and type definitions |
| `aeon/decorators` | Core decorator phase processing |
| `aeon/optimization` | Optimization passes |
| `aeon/llvm` | LLVM backend: lowering, code generation, GPU support |
| `aeon/bindings` | FFI bindings |
| `aeon/locations` | Source location tracking |
| `aeon/utils` | Shared utilities (names, locations, etc.) |

### Important distinction: Sugar vs Core

- **`STypes`/`STerm`** (in `aeon/sugar/`): Surface/sugar language types — safe to expose to users and tooling.
- **`Types`/`Term`** (in `aeon/core/`): Core language types — internal only, never exposed to users.

### Grammars

- `aeon/sugar/aeon_sugar.lark` — surface language grammar (user-facing)
- `aeon/core/aeon_core.lark` — core language grammar (used internally by tests and verification)

### Entry points

- CLI: `aeon/__main__.py` → `AeonDriver` (modes: parse/run/synth/lsp/format)
- Synthesis: `aeon/synthesis/entrypoint.py` identifies holes and routes to synthesizer backends

---

## Code style

- **Line length**: 120 characters (enforced by ruff and black)
- **Linting**: Ruff with E and F rule codes enabled (ignoring E741, E501)
- **Formatting**: Ruff formatter (black-compatible)
- **Type checking**: Strict mypy with custom stubs in `/stubs`. See `mypy.ini` for per-package overrides.
- **Runtime type checking**: pytest-beartype is enabled for the `aeon.core` package during tests
- **Python target**: 3.10+
- **Import cleanup**: pycln (remove unused imports)
- **Docstrings**: Google style (via docformatter)

---

## Test structure

Tests live in the `tests/` directory at the project root. Run them with `uv run pytest`.

### Conventions

- Test files are named `*_test.py` (e.g., `end_to_end_test.py`, `elaboration_test.py`).
- Test functions follow pytest conventions: `def test_*():`.
- A shared test driver (`tests/driver.py`) provides helpers like `check_compile()` and `check_compile_expr()` that run the full pipeline (parse → desugar → elaborate → lower → ANF → typecheck → evaluate) on inline Aeon source code.
- Test fixtures (`.ae` files) are stored in `tests/fixtures/`.
- Synthesis-specific tests are grouped under `tests/synthesis/`.

### Test categories

Tests cover each stage of the compiler pipeline and various language features:

- **Pipeline stages**: `elaboration_test.py`, `frontend_test.py`, `backend_test.py`, `infer_test.py`
- **Type system**: `liquid_test.py`, `liquid_typechecking_test.py`, `polymorphism_test.py`, `polytypes_test.py`, `typevars_test.py`, `wellformed_test.py`, `parametric_refinements_test.py`
- **Synthesis**: `tests/synthesis/` (grammar, intervals, capabilities, core extraction), `synth_fitness_test.py`, `synquid_*.py`, `tactic_synth_test.py`, `hole_test.py`
- **Verification**: `horn_test.py`, `smt_test.py`, `partial_vc_test.py`, `simplification_constraints_test.py`
- **Language features**: `match_inductive_test.py`, `recursion_test.py`, `termination_test.py`, `pow_test.py`, `decreasing_by_test.py`
- **End-to-end**: `end_to_end_test.py` (full pipeline tests with inline source)
- **LLVM backend**: `llvm_*.py` (lowering, generation, decorators, validation, GPU, end-to-end)
- **Other**: `lsp_test.py`, `optimization_test.py`, `pprint_test.py`, `equality_test.py`, `substitutions_test.py`, `native_test.py`

### What is the difference between the `STypes` and `Types` classes?

- The `Types` class represents the **Core Language**. These types are part of the internal implementation and should **never be exposed** to the user.

- The `STypes` class represents the **Sugar Language** (also called the **Surface Language**). These are types that are safe to expose and interact with in external code or tooling.
