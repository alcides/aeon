#!/bin/bash

SOURCE="${BASH_SOURCE[0]}"
while [ -h "$SOURCE" ]; do # resolve $SOURCE until the file is no longer a symlink
  DIR="$( cd -P "$( dirname "$SOURCE" )" >/dev/null 2>&1 && pwd )"
  SOURCE="$(readlink "$SOURCE")"
  [[ $SOURCE != /* ]] && SOURCE="$DIR/$SOURCE" # if $SOURCE was a relative symlink, we need to resolve it relative to the path where the symlink file was located
done
DIR="$( cd -P "$( dirname "$SOURCE" )" >/dev/null 2>&1 && pwd )"



parallel "python3 $DIR/synthesis_success.py --depth {1} --seed {2} --type \"{x:Int | x > 0 && x < 1000}\" --typename between0and1000 --totaltries 100 --manager {3}" ::: 4 5 6 7 8 9 10 11 12 ::: $(seq 1 30) ::: GrammaticalEvolution SemanticFilter Adaptive DepthAwareAdaptive
