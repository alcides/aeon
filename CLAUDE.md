# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aeon is a statically-typed programming language with native Liquid Types (refinement types), implemented as a Python interpreter with Python FFI. Developed at LASIGE, University of Lisbon.

## Repository Conventions

- Default branch is `master` (not `main`). Target `master` when opening pull requests and rebasing.

## Common Commands

```bash
# Install for development
uv pip install -e ".[dev]"
uvx pre-commit install

# Run tests
uv run pytest

# Run a single test
uv run pytest tests/end_to_end_test.py::test_name -x

# Run an .ae file
uv run python -m aeon [file.ae]

# Run with synthesis (type-directed BFS is the default; override with -s)
uv run python -m aeon --budget 10 -s tdsyn_enumerative examples/synthesis/example.ae

# Run all examples (used in CI)
bash run_examples.sh

# Linting/formatting (via pre-commit hooks)
uvx pre-commit run --all-files

# Type checking
uv run mypy aeon
```

**Synthesizer options (selected):** `tdsyn_enumerative` (default, type-directed BFS), `tdsyn_random`, `gp`, `synquid`, `random_search`, `enumerative`, `tactics`, `smt`, `sygus`, `llm` (needs `[llm]` extra). See `docs/synthesizers.md`.

## Code Style

- Line length: 120 (ruff + black)
- Ruff rules: E and F codes (ignoring E741, E501)
- Strict mypy with custom stubs in `/stubs`
- pytest-beartype enabled for `aeon.core` package
- Python 3.10+ target

## Import System

Aeon supports importing modules from multiple locations with the following search order:

1. **Current working directory** - for relative imports alongside your script
2. **`cwd/libraries/`** - backward compatibility for projects with a local libraries folder
3. **Package installation `libraries/`** - standard library modules (List, Math, Array, etc.)
4. **`AEONPATH` environment variable** - semicolon-separated custom library paths

This means you can run `python -m aeon /path/to/any/file.ae` from anywhere and it will find standard library imports.

**Import syntax:**
```aeon
import Math;              // Qualified import: use Math.abs
open Math                 // Unqualified: use abs directly
import Math (abs, pow);   // Selective import: use abs, pow directly
```

## Architecture

The codebase follows a compiler pipeline:

```
Source (.ae) → Parse (lark) → Sugar AST → Desugar → Elaborate → Lower to Core → Typecheck (z3 SMT) → Synthesize/Evaluate
```

`aeon/compilation/` owns the compile orchestration (parse → desugar → elaborate → lower → typecheck → link/cache). `aeon/facade/` is the product driver (CLI modes, synth, LLVM, decidability). ANF has been removed; existentials replace the old ANF pass (see `docs/design/existentials-replace-anf.md`).

### Key Packages

| Package | Role |
|---|---|
| `aeon/facade` | Product driver: `AeonDriver` / `AeonConfig` (run, synth, LSP, export) |
| `aeon/compilation` | Compile orchestration, import resolution, link/cache |
| `aeon/errors` | Leaf error hierarchy (imported by middle layers; re-exported from `aeon.facade.api`) |
| `aeon/sugar` | Surface language: AST (`STypes`/`STerm`), parser, desugaring (`desugar.py`, `typeclasses.py`, `inductives.py`) |
| `aeon/core` | Core language: `Types`/`Term` (internal representation), substitutions, liquid constraints |
| `aeon/elaboration` | Converts sugar AST to core AST with type elaboration |
| `aeon/typechecking` | Type inference and liquid type constraint verification |
| `aeon/verification` | SMT-based verification via z3: horn clauses, constraint solving |
| `aeon/synthesis` | Program synthesis backends |
| `aeon/backend` | Runtime evaluation |
| `aeon/lsp` | Language Server Protocol implementation (pygls) |
| `aeon/llvm` | LLVM CPU/CUDA backends |
| `aeon/libraries` | Standard library `.ae` files (List, Math, Image, etc.) |
| `aeon/prelude` | Built-in functions and type definitions |

### Important Distinction

- **`STypes`/`STerm`** (in `aeon/sugar/program.py`): Surface/sugar language types — safe to expose to users and tooling
- **`Types`/`Term`** (in `aeon/core/types.py`, `aeon/core/terms.py`): Core language types — internal only, never exposed to users

### Grammars

- `aeon/sugar/aeon_sugar.lark` — surface language grammar
- `aeon/core/aeon_core.lark` — core language grammar (used internally by tests and verification)

### Entry Points

- CLI: `aeon/__main__.py` → `AeonDriver` (modes: parse/run/synth/lsp/format)
- Synthesis: `aeon/synthesis/entrypoint.py` identifies holes and routes to synthesizer backends
