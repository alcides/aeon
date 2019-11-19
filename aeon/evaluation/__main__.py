import os
import shutil

from .evaluators.increasing_depth_evaluator import IncreasingDepthEvaluator
from .evaluators.regular_evaluator import RegularEvaluator

from aeon.evaluation.benchmark import generate_and_benchmark

def reset_folder(directory):
    if os.path.exists(directory):
        shutil.rmtree(directory)
    os.makedirs(directory)
        

def generate_data(evaluator):
    i = 0
    
    # Resets the output folder
    reset_folder(evaluator.path)

    for typee in evaluator.typees:
        file_name = '{}run_{}.csv'.format(evaluator.path, i)

        with open(file_name, 'w') as writer:
            generate_and_benchmark(typee, evaluator.get_depth(), 
                                    evaluator.POPULATION_SIZE, writer)
        i += 1

if __name__ == '__main__':
    # Get the evaluator
    evaluator = RegularEvaluator()
    # evaluator = IncreasingDepthEvaluator()

    # Generate the data with the evaluator path
    generate_data(evaluator)

    # Process the data
    evaluator.process()

    
