#!/usr/bin/env bash
# Scalability sweep: generate a robustness query at each (inputs, hidden)
# size, verify it with a wall-clock timeout, and record time + verdict.
set -u
cd "$(dirname "$0")/../../.."   # repo root
RES="examples/nn/mnist/results.tsv"
TIMEOUT="${TIMEOUT:-200}"
EPS="${EPS:-0.02}"
printf "inputs\thidden\trelus\tsecs\tverdict\n" > "$RES"

# downsample -> input count: 4->4, 2->16, 1->64
for ds in 4 2 1; do
  case $ds in 4) nin=4;; 2) nin=16;; 1) nin=64;; esac
  for H in 2 4 8 16 32; do
    ae="examples/nn/mnist/sweep_${nin}_${H}.ae"
    uv run python examples/nn/mnist/gen.py --hidden "$H" --downsample "$ds" \
        --eps "$EPS" --sample 0 > "$ae" 2>/dev/null
    start=$(date +%s)
    out=$(timeout "$TIMEOUT" uv run python -m aeon "$ae" 2>&1)
    code=$?
    end=$(date +%s)
    secs=$((end - start))
    if [ $code -eq 124 ]; then
      verdict="TIMEOUT(>${TIMEOUT}s)"
    elif echo "$out" | grep -qiE "type error|failed to prove"; then
      verdict="not-robust(rejected)"
    elif echo "$out" | grep -qE "^0$"; then
      verdict="ROBUST(verified)"
    else
      verdict="ERROR"
    fi
    printf "%s\t%s\t%s\t%s\t%s\n" "$nin" "$H" "$H" "$secs" "$verdict" | tee -a "$RES"
    rm -f "$ae"
    # Stop escalating hidden width once we time out at this input size.
    if [ $code -eq 124 ]; then break; fi
  done
done
echo "DONE"
