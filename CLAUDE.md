# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Aeon is a statically-typed programming language with native Liquid Types (refinement types), implemented as a Python interpreter with Python FFI. Developed at LASIGE, University of Lisbon.

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

# Run with synthesis (genetic programming, 60s default budget)
uv run python -m aeon --budget 10 -s gp examples/synthesis/example.ae

# Run all examples (used in CI)
bash run_examples.sh

# Linting/formatting (via pre-commit hooks)
uvx pre-commit run --all-files

# Type checking
uvx ty check
```

**Synthesizer options:** `gp` (genetic programming, default), `synquid`, `random_search`, `enumerative`, `hc` (hill climbing), `1p1` (one plus one)

## Code Style

- Line length: 120 (ruff + black)
- Ruff rules: E and F codes (ignoring E741, E501)
- Type checking with ty (Astral's type checker)
- pytest-beartype enabled for `aeon.core` package
- Python 3.10+ target

## Architecture

The codebase follows a compiler pipeline:

```
Source (.ae) → Parse (lark) → Sugar AST → Desugar/Elaborate → Core AST → ANF → Typecheck (z3 SMT) → Synthesize/Evaluate
```

### Key Packages

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
| `aeon/lsp` | Language Server Protocol implementation (pygls v2.1.0) |
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
