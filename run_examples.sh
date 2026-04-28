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

for folder in ffi image imports list syntax synthesis "PSB2/solved" "llvm/cpu/test" "llvm/gpu/test";
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
