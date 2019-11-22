if hash pypy3 2>/dev/null; then
    PY=pypy3
else
    PY=python3
fi

for d in {0..15}
do
    for i in {0..10}
    do
        $PY -m aeon.evaluation record $i $d &
    done
done

wait

python3 -m aeon.evaluation plot
