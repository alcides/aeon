import sys
import os
import random
import shutil

# python3.7 -m conversor examples/conversion/ex000.ae
sys.path.append('..')

from aeon.frontend import parse
from conversor.convert import convert

if __name__ == '__main__':

    ast = parse(sys.argv[-1])
    ast = convert(ast)
