# AGENTS.md

## Cursor Cloud specific instructions

### Environment

- Python 3.12+ with `uv` package manager.
- The project uses a virtual environment at `/workspace/.venv`. Activate it with `source /workspace/.venv/bin/activate` before running commands.
- All commands documented in `CLAUDE.md` apply; use `pytest` for tests, `pre-commit run --all-files` for linting, and `python -m aeon <file.ae>` to run programs.

### Gotchas

- **git hooks path**: If `pre-commit install` fails with "Cowardly refusing to install hooks with `core.hooksPath` set", run `git config --unset-all core.hooksPath` first.
- **System pip permissions**: Do not use `uv pip install --system` — it will fail with permission errors on `/usr/local/bin`. Always install into the venv.
- **No external services required**: Aeon is fully self-contained (Z3 solver is a pip package). The only optional dependency is Ollama for LLM-based synthesis, which is not needed for standard development/testing.

### Running the application

```bash
# Hello world
python -m aeon examples/syntax/hello_world_main.ae

# With synthesis (genetic programming, 5s budget)
python -m aeon --budget 5 -s gp examples/synthesis/int.ae

# Run all examples (integration test)
bash run_examples.sh
```

### Testing

```bash
pytest                          # Full test suite (~415 tests, ~2 min)
pytest tests/some_test.py -x   # Single test file, stop on first failure
pre-commit run --all-files     # Lint + format + type check
```
