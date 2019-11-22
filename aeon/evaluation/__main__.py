import os
import sys
import shutil

from aeon.evaluation import *
from aeon.evaluation.benchmark import generate_and_benchmark


def reset_folder(directory):
    if os.path.exists(directory):
        shutil.rmtree(directory)
    os.makedirs(directory)


def generate_data(typees_selection, depth_selection):
    for depth in depth_selection:
        for run in range(RUNS):
            for (typee, pretty_typee, wrapper) in typees_selection:
                file_name = '{}typee{}_depth{}_run{}.csv'.format(
                    OUTPUT_PATH, pretty_typee, depth, run)

                with open(file_name, 'w') as writer:
                    generate_and_benchmark(typee, pretty_typee, depth,
                                           POPULATION_SIZE, writer, wrapper)


def run_evaluator(evaluator):
    reset_folder(evaluator.path)
    evaluator.process()


if __name__ == '__main__':

    if len(sys.argv) >= 1 or sys.argv[1] == 'record':
        # Reset the output directory
        #reset_folder(OUTPUT_PATH)
        typees_selection = [typees[int(sys.argv[2])]
                            ] if len(sys.argv) >= 2 else typees
        depth_selection = [int(sys.argv[3])] if len(sys.argv) >= 3 else range(
            MIN_TREE_DEPTH, MAX_TREE_DEPTH)
        # Generate the data with the evaluator path
        generate_data(typees_selection, depth_selection)
    else:
        from .evaluators.regular_evaluator import RegularEvaluator
        from .evaluators.int_double_distr_evaluator import IntDoubleDistrEvaluator
        from .evaluators.increasing_depth_evaluator import IncreasingDepthEvaluator

        # Run the evaluator
        run_evaluator(RegularEvaluator())
        run_evaluator(IntDoubleDistrEvaluator())
        run_evaluator(IncreasingDepthEvaluator())
