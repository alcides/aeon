import os
import sys
import shutil

from aeon.evaluation import *
from aeon.evaluation.benchmark import generate_and_benchmark


def reset_folder(directory):
    if os.path.exists(directory):
        shutil.rmtree(directory)
    os.makedirs(directory)


def generate_data():
    for depth in range(MIN_TREE_DEPTH, MAX_TREE_DEPTH):
        for run in range(RUNS):
            for (typee, wrapper) in typees:
                file_name = '{}typee{}_depth{}_run{}.csv'.format(
                    OUTPUT_PATH, run, depth, run)

                with open(file_name, 'w') as writer:
                    generate_and_benchmark(typee, depth, POPULATION_SIZE,
                                           writer, wrapper)


def run_evaluator(evaluator):
    reset_folder(evaluator.path)
    evaluator.process()


if __name__ == '__main__':

    if '__pypy__' in sys.builtin_module_names:
        # Reset the output directory
        reset_folder(OUTPUT_PATH)

        # Generate the data with the evaluator path
        generate_data()
    else:
        from .evaluators.regular_evaluator import RegularEvaluator
        from .evaluators.int_double_distr_evaluator import IntDoubleDistrEvaluator
        from .evaluators.increasing_depth_evaluator import IncreasingDepthEvaluator

        # Run the evaluator
        run_evaluator(RegularEvaluator())
        run_evaluator(IntDoubleDistrEvaluator())
        run_evaluator(IncreasingDepthEvaluator())
