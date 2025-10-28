#!/bin/bash
export PYTHONPATH="${PYTHONPATH:+${PYTHONPATH}:}."

set -o errexit
set -o nounset
set -o pipefail
if [[ "${TRACE-0}" == "1" ]]; then
    set -o xtrace
fi

cd "$(dirname "$0")"

function run_example {
    printf "Running %s ..." "${@}"
    uv run python -m aeon --no-main --budget 10 "$@" > /dev/null
    RESULT=$?
    if [ $RESULT -eq 0 ]; then
        echo "(success)"
    else
        echo "(failed)"
        exit 111
    fi
}

for folder in ffi image imports list syntax synthesis "PSB2/solved";
do
    for entry in examples/$folder/*.ae
    do
        run_example "$entry"
    done
done
