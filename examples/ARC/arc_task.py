from typing import List, Tuple, Callable
import numpy as np
from abc import ABC
from dataclasses import dataclass
from geneticengine.grammar import Grammar
from geneticengine.grammar.decorators import weight
from geneticengine.prelude import abstract
from geneticengine.problems import SingleObjectiveProblem
from geneticengine.algorithms.gp.operators.combinators import ParallelStep, SequenceStep
from geneticengine.algorithms.gp.operators.crossover import GenericCrossoverStep
from geneticengine.algorithms.gp.operators.mutation import GenericMutationStep
from geneticengine.algorithms.gp.operators.selection import TournamentSelection
from geneticengine.algorithms.gp.operators.elitism import ElitismStep
from geneticengine.algorithms.gp.operators.novelty import NoveltyStep
from geneticengine.prelude import GeneticProgramming
from geneticengine.random.sources import NativeRandomSource
from geneticengine.evaluation.budget import TimeBudget
from geneticengine.representations.tree.treebased import TreeBasedRepresentation
from geneticengine.representations.tree.initializations import MaxDepthDecider
from geneticengine.grammar.grammar import extract_grammar
from aeon.bindings.task_dsl import (
    Grid, Example, Task,
    mirror_horizontal, mirror_vertical,
    glue_horizontal, glue_vertical,
    load_arc_task_by_id, evaluate_on_train_impl, evaluate_on_test_impl
)

class GridTransform(ABC):
    def apply(self, grid: Grid) -> Grid:
        pass
    
    def __str__(self) -> str:
        return self.__class__.__name__

class MirrorHorizontal(GridTransform):
    def apply(self, grid: Grid) -> Grid:
        return mirror_horizontal(grid)

class MirrorVertical(GridTransform):
    def apply(self, grid: Grid) -> Grid:
        return mirror_vertical(grid)

@dataclass
class GlueHorizontal(GridTransform):
    left: GridTransform
    right: GridTransform

    def apply(self, grid: Grid) -> Grid:
        left_result = self.left.apply(grid)
        right_result = self.right.apply(grid)
        try:
            return glue_horizontal(left_result, right_result)
        except AssertionError:
            # If the grids can't be combined horizontally, return the original grid
            return grid
    
    def __str__(self) -> str:
        return f"GlueHorizontal({self.left}, {self.right})"

@dataclass
class GlueVertical(GridTransform):
    top: GridTransform
    bottom: GridTransform

    def apply(self, grid: Grid) -> Grid:
        top_result = self.top.apply(grid)
        bottom_result = self.bottom.apply(grid)
        try:
            return glue_vertical(top_result, bottom_result)
        except AssertionError:
            # If the grids can't be combined vertically, return the original grid
            return grid
    
    def __str__(self) -> str:
        return f"GlueVertical({self.top}, {self.bottom})"

@dataclass
class Compose(GridTransform):
    first: GridTransform
    second: GridTransform

    def apply(self, grid: Grid) -> Grid:
        intermediate = self.first.apply(grid)
        return self.second.apply(intermediate)
    
    def __str__(self) -> str:
        return f"Compose({self.first}, {self.second})"

class Identity(GridTransform):
    def apply(self, grid: Grid) -> Grid:
        return grid

def create_program(transform: GridTransform) -> Callable[[Grid], Grid]:
    def program(grid: Grid) -> Grid:
        return transform.apply(grid)
    return program

def solve_task(task_id: str, max_depth: int = 5, population_size: int = 100, time_limit: int = 60):
    # Load the task
    task = load_arc_task_by_id(task_id)
    
    # Create the grammar
    grammar = extract_grammar([GridTransform, MirrorHorizontal, MirrorVertical, GlueHorizontal, GlueVertical, Compose, Identity], GridTransform)
    
    # Define the fitness function
    def train_fitness_function(individual: GridTransform) -> float:
        program = create_program(individual)
        return evaluate_on_train_impl(program, task)  # Convert to minimization problem
    
    def test_fitness_function(individual: GridTransform) -> float:
        program = create_program(individual)
        return evaluate_on_test_impl(program, task)
    
    # Create the problem
    problem = SingleObjectiveProblem(
        fitness_function=train_fitness_function,
        minimize=False
    )
    
    # Configure GP parameters
    gp_params = {
        "population_size": population_size,
        "n_elites": 1,
        "novelty": 1,
        "probability_mutation": 0.01,
        "probability_crossover": 0.9,
        "tournament_size": 5,
        "timer_limit": time_limit
    }
    
    # Create the GP step
    gp_step = ParallelStep([
        ElitismStep(),
        NoveltyStep(),
        SequenceStep(
            TournamentSelection(gp_params["tournament_size"]),
            GenericCrossoverStep(gp_params["probability_crossover"]),
            GenericMutationStep(gp_params["probability_mutation"])
        )
    ], weights=[
        gp_params["n_elites"],
        gp_params["novelty"],
        gp_params["population_size"] - gp_params["n_elites"] - gp_params["novelty"]
    ])
    
    # Create and run the algorithm
    alg = GeneticProgramming(
        problem=problem,
        budget=TimeBudget(time=gp_params["timer_limit"]),
        representation=TreeBasedRepresentation(grammar, decider=MaxDepthDecider(NativeRandomSource(42), grammar, max_depth=max_depth)),
        random=NativeRandomSource(42),
        population_size=gp_params["population_size"],
        step=gp_step
    )
    
    # Run the search
    best_individuals = alg.search()
    best_individual = best_individuals[0]  # Get the first (best) individual from the list
    
    print("\nBest solution found:")
    print(f"Train fitness: {best_individual.get_fitness(problem)}")
    print(f"Test fitness: {test_fitness_function(best_individual.get_phenotype())}")
    print("\nSolution tree:")
    print(best_individual.get_phenotype())
    
    # Create and return the final program
    return create_program(best_individual)

if __name__ == "__main__":
    # Solve the specific task
    program = solve_task("3af2c5a8")
