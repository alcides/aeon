# AGENTS.md

## Cursor Cloud specific instructions

### Quick Start

The update script handles all dependency installation and runs `pre-commit run --all-files` to pre-cache hook environments. After it runs, activate the venv and you're ready:

```bash
source /workspace/.venv/bin/activate
```

Pre-commit hooks are installed as a git pre-commit hook — they run automatically on every `git commit`. If hooks fail, the commit is rejected. Always ensure `pre-commit run --all-files` passes before committing.

All dev commands are documented in `CLAUDE.md`. Key ones:

| Task | Command |
|------|---------|
| Run tests | `pytest` |
| Run single test | `pytest tests/<file>.py::<test> -x` |
| Lint + format + typecheck | `pre-commit run --all-files` |
| Type check only | `mypy aeon --no-strict-optional --ignore-missing-imports` |
| Run .ae file | `python -m aeon <file.ae>` |
| Run with synthesis | `python -m aeon --budget 10 -s gp examples/synthesis/<file>.ae` |
| Run all examples (CI) | `bash run_examples.sh` |

### Gotchas

- **git hooks path**: If `pre-commit install` fails with "Cowardly refusing to install hooks with `core.hooksPath` set", run `git config --unset-all core.hooksPath` first.
- **System pip permissions**: Never use `uv pip install --system`. Always install into `/workspace/.venv`.
- **No external services**: Aeon is fully self-contained. Z3 solver is a pip package, not a service. Ollama (LLM synthesis) is optional and not needed for tests.
- **pre-commit first run**: Pre-commit hook environments are cached after first execution. First `pre-commit run --all-files` takes ~90s; subsequent runs are fast.
- **pytest duration**: Full test suite (~415 tests) takes ~2 minutes. Use `-x` flag and specific test files for faster iteration.
- **`run_examples.sh` uses `uv run`**: The script calls `uv run python -m aeon`. This works because the package is installed in editable mode via the venv.

### Architecture (for quick orientation)

See `CLAUDE.md` for full architecture docs. The compiler pipeline is:

```
Source (.ae) → Parse (lark) → Sugar AST → Desugar/Elaborate → Core AST → ANF → Typecheck (z3 SMT) → Synthesize/Evaluate
```

Entry point: `aeon/__main__.py` → `AeonDriver` in `aeon/facade/`. Synthesis uses `aeon/synthesis/entrypoint.py`.
