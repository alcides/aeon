PY=python3

for d in {0..9}
do
    for i in {0..10}
    do
        $PY -m aeon.evaluation record $i $d &
    done
done

wait

python3 -m aeon.evaluation plot
