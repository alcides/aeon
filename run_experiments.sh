# run processes and store pids in array
for i in `seq 0 29`; do
    ./ae --seed=${i} examples/automatic/file.ae > dtgp_${i}.log &> dtgp_${i}.err  &
    pids[${i}]=$!
    
    ./ae --seed=${i} --norefine examples/automatic/file.ae > stgp_${i}.log &> stgp_${i}.err  &
    pids[${i}]=$!
done

# wait for all pids
for pid in ${pids[*]}; do
    wait $pid
done