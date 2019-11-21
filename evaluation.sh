if hash pypy3 2>/dev/null; then
    pypy3 -m aeon.evaluation record
else
    python3 -m aeon.evaluation record
fi
python3 -m aeon.evaluation plot
