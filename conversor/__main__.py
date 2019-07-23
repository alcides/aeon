import sys
import os
import random
import shutil
import ntpath

# python3.7 -m conversor examples/conversion/ex000.ae
sys.path.append('..')

from aeon.frontend import parse
from conversor.convert import convert

if __name__ == '__main__':

    ast = parse(sys.argv[-1])
    converted = convert(ast)

    filename = ntpath.basename(sys.argv[-1])
    file = open('examples/converted/' + filename, 'w')

    for line in converted:
        file.write(line)
        file.write("\r\n\r\n")
