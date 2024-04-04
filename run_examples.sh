#!/bin/bash
export PYTHONPATH="${PYTHONPATH:+${PYTHONPATH}:}."

PYTHON_BINARY=python3

set -o errexit
set -o nounset
set -o pipefail
if [[ "${TRACE-0}" == "1" ]]; then
    set -o xtrace
fi

cd "$(dirname "$0")"

function run_example {
    printf "Running $1..."
    $PYTHON_BINARY -m aeon $1 > /dev/null
    RESULT=$?
    if [ $RESULT -eq 0 ]; then
        echo "(success)"
    else
        echo "(failed)"
        exit 111
    fi

}

# Should be somewhere else (maybe add to unit tests)
# run_example examples/simple_choice_of_choice.py

run_example --core examples/core/abs_main.ae
run_example --core examples/core/anf_stress_main.ae
run_example --core examples/core/factorial_main.ae
run_example --core examples/core/fib_main.ae
run_example --core examples/core/hello.ae
run_example --core examples/core/if_example.ae
run_example --core examples/core/max.ae
run_example --core examples/core/native_main.ae
