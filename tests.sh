 if [ "$#" -ne 1 ]; then
    python3 -m unittest discover -t . -s aeon2/tests
 else
    python3 -m unittest aeon2.tests.$1
 fi

