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
    printf "Running ${@} ..."
    $PYTHON_BINARY -m aeon $@ > /dev/null
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


core_examples=examples/core
for entry in "$core_examples"/*.ae
do
  run_example --core "$entry"
done

# TODO: add pbt PSB2
for folder in ffi image imports list syntax synthesis;
do
    for entry in examples/$folder/*.ae
    do
    run_example "$entry"
    done
done
