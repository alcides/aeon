#!/bin/bash
export PYTHONPATH="${PYTHONPATH:+${PYTHONPATH}:}."

set -o errexit
set -o nounset
set -o pipefail
if [[ "${TRACE-0}" == "1" ]]; then
    set -o xtrace
fi

cd "$(dirname "$0")"

# Number of parallel jobs: as many as the machine has cores.
if command -v nproc > /dev/null 2>&1; then
    NCORES=$(nproc)
elif command -v sysctl > /dev/null 2>&1; then
    NCORES=$(sysctl -n hw.ncpu)
else
    NCORES=4
fi

# Worker that runs a single example. Kept self-contained (rather than an
# exported function) so it survives across differing bash versions invoked by
# xargs. A complete line is printed at once so parallel output doesn't interleave.
read -r -d '' RUN_ONE <<'EOF' || true
f="$1"
RESULT=0
uv run python -m aeon --no-main --budget 10 "$f" > /dev/null 2>&1 || RESULT=$?
if [ "$RESULT" -eq 0 ]; then
    printf "Running %s ...(success)\n" "$f"
elif [ "$RESULT" -eq 2 ]; then
    printf "Running %s ...(no solution found, but OK)\n" "$f"
else
    printf "Running %s ...(failed)\n" "$f"
    exit 111
fi
EOF

status=0
for folder in ffi image imports list mutual syntax synthesis synthesis/image_edits verification "PSB2/solved" 99problems;
do
    for entry in examples/$folder/*.ae
    do
        printf '%s\0' "$entry"
    done
done | xargs -0 -P "$NCORES" -I {} bash -c "$RUN_ONE" _ {} || status=$?

if [ "$status" -ne 0 ]; then
    echo "Some examples failed."
    exit 111
fi

# Property-based testing examples (issue #37), @example assertions, and the
# Testing-library unit/property suites: run with --test; every property and
# example must pass (exit code 0).
for entry in examples/pbt/props_*.ae examples/pbt/examples_*.ae examples/testing/*.ae
do
    printf "Running (pbt) %s ..." "$entry"
    if uv run python -m aeon --test "$entry" > /dev/null 2>&1; then
        printf "(success)\n"
    else
        printf "(failed)\n"
        echo "Some property-based tests failed."
        exit 111
    fi
done
