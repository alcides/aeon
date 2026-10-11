#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
exec uv run --extra image python scripts/run_examples.py "$@"
