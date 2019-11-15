from aeon.frontend2 import expr, typee

from aeon.evaluation.benchmark import *
from aeon.evaluation.process_data import process

ex = expr.parse_strict
ty = typee.parse_strict

typees = [
    ty('Boolean'),
    ty('Integer'),
    ty('{x:Integer where (x > 0)}')
]

if __name__ == '__main__':
    i = 0
    folder_name = 'aeon/evaluation/results/'
    for typee in typees:
        print('=' * 30)
        print('Typee:', typee, '\n')
        file_name = '{}/typee_{}.csv'.format(folder_name, i) 
        # Generate and benchmark typee
        with open(file_name, 'w') as file_writer:
            generate_and_benchmark(typee, file_writer)
        i += 1
    
    # Process the csvs into plots
    process(folder_name)