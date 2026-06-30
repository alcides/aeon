#!/usr/bin/env bash
#
# Idempotent dependency setup for Aeon Cursor Cloud agents.
#
# Referenced as the `install` command in .cursor/environment.json, so it runs on
# every cloud-agent VM boot (after the latest changes are pulled). It must be
# safe to run repeatedly and on a partially-cached filesystem.
#
# What it does:
#   1. Ensures `uv` (the project's package manager) is on PATH.
#   2. Creates the project virtualenv at /workspace/.venv. We use `uv venv`
#      rather than `python3 -m venv` because the base image's system Python
#      ships without `ensurepip`, so the stdlib venv module fails.
#   3. Installs Aeon in editable mode plus the test/lint toolchain.
#   4. Pre-caches the pre-commit hook environments (the first run is slow;
#      subsequent runs are fast).
#
# After this runs, an interactive shell only needs:
#   source /workspace/.venv/bin/activate
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel 2>/dev/null || echo /workspace)"
cd "$ROOT"

export PATH="$HOME/.local/bin:$PATH"

# 1. Ensure uv is available. Try the standalone installer first (no assumptions
#    about pip or an active virtualenv); fall back to pip in its various flavours
#    so this works whether or not a venv happens to be active.
if ! command -v uv >/dev/null 2>&1; then
    echo "[install] uv not found; bootstrapping ..."
    if command -v curl >/dev/null 2>&1; then
        curl -LsSf https://astral.sh/uv/install.sh | sh || true
    fi
    export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
fi
if ! command -v uv >/dev/null 2>&1; then
    python3 -m pip install --user uv \
        || python3 -m pip install --user --break-system-packages uv \
        || python3 -m pip install --break-system-packages uv
fi
export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"

# 2. Create the venv if it does not already exist.
if [ ! -x .venv/bin/python ]; then
    echo "[install] creating virtualenv at .venv ..."
    uv venv .venv
fi
# shellcheck disable=SC1091
source .venv/bin/activate

# 3. Install Aeon (editable) plus the test and lint toolchain. `[tests]` brings
#    in pytest + pytest-beartype; pre-commit/mypy/ruff are the lint stack the
#    repo's pre-commit hooks use.
echo "[install] installing Aeon and dependencies ..."
uv pip install -e ".[tests]"
uv pip install pre-commit mypy ruff

# 4. Pre-cache pre-commit hook environments. We use `pre-commit run` rather than
#    `pre-commit install` so we do not clobber the cloud harness's managed git
#    hooksPath; running the hooks once is enough to populate their cached envs.
echo "[install] warming pre-commit hook environments ..."
pre-commit run --all-files || true

echo "[install] done."
