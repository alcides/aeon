import sys
import os
import random
import shutil
import logging

from aeon.frontend import parse, parse_strict
from aeon.frontend_core import parse as parse2
from aeon.typechecker import check_program
from aeon.deducer import deducer
from aeon.interpreter import run
from aeon.automatic import automatic
from aeon.translator import translate

sys.setrecursionlimit(sys.getrecursionlimit() * 5)

if __name__ == '__main__':

    debug = '-d' in sys.argv

    level = logging.DEBUG if debug else logging.WARN

    # Set the logging configuration
    logging.basicConfig(format='%(asctime)s %(levelname)-8s [%(filename)s:' \
    '%(lineno)d]\t%(message)s', datefmt='%Y-%m-%d:%H:%M:%S', level=level)
    
    logging.debug("="*80)
    logging.debug("Starting the debugger...")
    
    for arg in sys.argv:
        if arg.startswith("--seed="):
            seed = int(arg[7:])
            random.seed(seed)
            logging.debug(f"Random seed set to {seed}")
    
    fname = sys.argv[-1]

    if fname.endswith(".ae2"):
        logging.debug("Parsing the AeonCore language")
        ast = parse2(fname)
    else:
        logging.debug("Parsing the Aeon language")
        ast = parse(fname)

    try:
        logging.debug("="*80)
        logging.debug("Typechecking the program")   
        
        ast, context, holed = check_program(ast)
            
        # Infer the holes
        if holed:
            logging.debug("Deducing the type of the holes")
            logging.debug(f"Before deducing: {holed}")
            
            ast, context, holed = deducer(ast, context, holed)
            logging.debug(f"After deducing: {holed}")

            # If there are holes, lets fill them
            logging.debug("="*80)
            logging.debug("Evolutionary synthesis of the program")
            #ast = automatic(ast, context, holed)

    except Exception as t:
        raise t
        sys.exit(-1)

    logging.info("="*80)
    logging.info(f"Running the program {sys.argv[-1]}")

    run(ast)
