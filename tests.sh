 if [ "$#" -ne 1 ]; then
    pypy3 -m unittest discover -t . -s aeon/tests
 else
    pypy3 -m unittest aeon.tests.$1
 fi

