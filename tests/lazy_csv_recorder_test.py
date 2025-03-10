import csv
import os
import tempfile
import time

from geneticengine.problems import Problem

from aeon.synthesis_grammar.synthesizer import LazyCSVRecorder


class MockFitness:
    def __init__(self, components: list[float]):
        self.fitness_components = components
        self.maximizing_aggregate = sum(components)


class MockIndividual:
    def get_fitness(self, problem: Problem) -> MockFitness:
        return MockFitness([1.0, 2.0])

    def get_phenotype(self) -> str:
        return "mock_phenotype"


class MockProblem:
    def number_of_objectives(self) -> int:
        return 2


class MockTracker:
    def __init__(self):
        self.start_time = time.monotonic_ns()


def test_lazy_csv_recorder_with_different_two_different_fitness_components():
    with tempfile.NamedTemporaryFile(delete=False, mode="w", newline="") as temp_file:
        temp_file_path = temp_file.name

    try:
        problem = MockProblem()
        recorder = LazyCSVRecorder(temp_file_path, problem)  # type: ignore
        tracker = MockTracker()
        individual = MockIndividual()

        recorder.register(tracker, individual, problem, is_best=True)  # type: ignore
        recorder.csv_file.close()

        with open(temp_file_path, "r", newline="") as f:
            reader = csv.reader(f)
            rows = list(reader)

        assert len(rows) == 2, "Expected two rows in the CSV file."

        header = rows[0]
        data_row = rows[1]

        assert "Fitness0" in header and "Fitness1" in header

        fitness0 = float(data_row[header.index("Fitness0")])
        fitness1 = float(data_row[header.index("Fitness1")])

        # The bug: both "Fitness0" and "Fitness1" will be 2.0
        assert fitness0 != fitness1, "Expected fitness values to be different."
        assert fitness0 == 1.0, "Expected fitness value for 'Fitness0' is 1.0."
        assert fitness1 == 2.0, "Expected fitness value for 'Fitness1' is 2.0."

    finally:
        os.remove(temp_file_path)
