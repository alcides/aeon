import os
import shutil

from aeon.evaluation import *
from aeon.evaluation.benchmark import generate_and_benchmark

from .evaluators.regular_evaluator import RegularEvaluator
from .evaluators.int_double_distr_evaluator import IntDoubleDistrEvaluator
from .evaluators.increasing_depth_evaluator import IncreasingDepthEvaluator


def reset_folder(directory):
    if os.path.exists(directory):
        shutil.rmtree(directory)
    os.makedirs(directory)


def generate_data():
    for depth in range(1, MAX_TREE_DEPTH):
        for run in range(RUNS):
            for typee in typees:
                file_name = '{}typee{}_depth{}_run{}.csv'.format(
                    OUTPUT_PATH, run, depth, run)

                with open(file_name, 'w') as writer:
                    generate_and_benchmark(typee, depth, POPULATION_SIZE,
                                           writer)


def run_evaluator(evaluator):
    reset_folder(evaluator.path)
    evaluator.process()


if __name__ == '__main__':

    # Reset the output directory
    reset_folder(OUTPUT_PATH)

    # Generate the data with the evaluator path
    generate_data()

    # Run the evaluator
    run_evaluator(RegularEvaluator())
    run_evaluator(IntDoubleDistrEvaluator())
    run_evaluator(IncreasingDepthEvaluator())