#!/usr/bin/env bash
set -euo pipefail
run_dir=$1
python_bin=$2
offset=${3:-0}
# Slurm copies the batch script to its spool; derive the project from the plan path.
project_dir=$("$python_bin" -c 'import sys,pathlib; p=pathlib.Path(sys.argv[1]); print(next(x for x in p.parents if (x/"scripts/eval.py").is_file()))' "$run_dir")
exec "$python_bin" "$project_dir/scripts/eval.py" run --run "$run_dir" --python "$python_bin" --index "$((offset + SLURM_ARRAY_TASK_ID))"
