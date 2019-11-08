 if [ "$#" -ne 1 ]; then
    python3 -m unittest discover -t . -s aeon/tests
 else
    python3 -m unittest aeon.tests.$1
 fi

