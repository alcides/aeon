from aeon.frontend2 import expr, typee
from aeon.metrics.benchmark import *

ex = expr.parse_strict
ty = typee.parse_strict

typees = [
    ty('Boolean'),
    ty('Integer'),
    ty('{x:Integer where (x > 0)}')
]

if __name__ == '__main__':
    i = 0
    for typee in typees:
        print('=' * 30)
        print('Typee:', typee, '\n')
        file_name = 'aeon/metrics/results/typee_{}.csv'.format(i)
        with open(file_name, 'w') as file_writer: 
            # Generate and benchmark typee
            generate_and_benchmark(typee, file_writer)
        i += 1