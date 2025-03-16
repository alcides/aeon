import csv
import time
from io import TextIOWrapper
from typing import Optional, Any

from geneticengine.evaluation.recorder import SearchRecorder, FieldMapper
from geneticengine.problems import Problem
from geneticengine.solutions import Individual


class LazyCSVRecorder(SearchRecorder):

    def __init__(
        self,
        csv_path: str,
        problem: Problem,
        fields: dict[str, FieldMapper] = None,
        extra_fields: dict[str, FieldMapper] = None,
        only_record_best_individuals: bool = True,
    ):
        assert csv_path is not None
        self.csv_writer: Optional[Any] = None
        self.csv_file: Optional[TextIOWrapper] = None
        self.csv_file_path = csv_path
        self.fields = fields
        self.extra_fields = extra_fields
        self.only_record_best_individuals = only_record_best_individuals
        self.problem = problem
        self.header_printed = False
        if fields is not None:
            self.fields = fields

    def register(self, tracker: Any, individual: Individual, problem: Problem, is_best=True):
        if self.csv_file is None:
            self.csv_file = open(self.csv_file_path, "w", newline="")
            self.csv_writer = csv.writer(self.csv_file)
            if self.fields is None:
                self.fields = {
                    "Execution Time": lambda t, i, _: (time.monotonic_ns() - t.start_time) * 0.000000001,
                    "Fitness Aggregated": lambda t, i, p: i.get_fitness(p).maximizing_aggregate,
                    "Phenotype": lambda t, i, _: i.get_phenotype(),
                    "Fitness": lambda t, i, p: i.get_fitness(p).fitness_components,
                }

            if self.extra_fields is not None:
                for name in self.extra_fields:
                    self.fields[name] = self.extra_fields[name]
            self.csv_writer.writerow([name for name in self.fields])
            self.csv_file.flush()
        if not self.only_record_best_individuals or is_best:
            self.csv_writer.writerow(
                [self.fields[name](tracker, individual, problem) for name in self.fields],
            )
            self.csv_file.flush()


class CSVRecorder(SearchRecorder):

    def __init__(
        self,
        csv_path: str,
        problem: Problem,
        fields: dict[str, FieldMapper] = None,
        extra_fields: dict[str, FieldMapper] = None,
        only_record_best_individuals: bool = True,
    ):
        assert csv_path is not None
        self.csv_file = open(csv_path, "w", newline="")
        self.csv_writer = csv.writer(self.csv_file)
        if fields is not None:
            self.fields = fields
        else:
            self.fields = {
                "Execution Time": lambda t, i, _: (time.monotonic_ns() - t.start_time) * 0.000000001,
                "Fitness Aggregated": lambda t, i, p: i.get_fitness(p).maximizing_aggregate,
                "Phenotype": lambda t, i, _: i.get_phenotype(),
                "Fitness": lambda t, i, p: i.get_fitness(p).fitness_components,
            }
            for comp in range(problem.number_of_objectives()):
                self.fields[f"Fitness{comp}"] = lambda t, i, p: i.get_fitness(p).fitness_components[comp]
        if extra_fields is not None:
            for name in extra_fields:
                self.fields[name] = extra_fields[name]
        self.csv_writer.writerow([name for name in self.fields])
        self.csv_file.flush()
        self.header_printed = False
        self.only_record_best_individuals = only_record_best_individuals

    def register(self, tracker: Any, individual: Individual, problem: Problem, is_best=True):
        if not self.only_record_best_individuals or is_best:
            self.csv_writer.writerow(
                [self.fields[name](tracker, individual, problem) for name in self.fields],
            )
            self.csv_file.flush()
