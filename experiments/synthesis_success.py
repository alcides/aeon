import pathlib
import sys
import random
import time
from typing import Callable

experiments_folder = pathlib.Path(__file__).parent
sys.path.append(str(experiments_folder.parent.absolute()))

from aeon.synthesis.exceptions import NoMoreBudget
from aeon.typing.context import EmptyContext
from aeon.synthesis.sources import ListRandomSource
from aeon.frontend.parser import parse_term, parse_type
from aeon.synthesis.term_synthesis import synth_term
from aeon.synthesis.type_synthesis import synth_type
from aeon.synthesis.choice_manager import (
    DepthAwareManager,
    DynamicProbManager,
    ChoiceManager,
)

type_tries = 100
term_tries = 100


def generate_lists(n, seed=1234):
    r = random.Random(seed)
    for _ in range(n):
        size = r.randint(1, 50)
        yield [r.randint(-256, 256) for _ in range(size)]


def evaluate_type(mang: Callable[[], ChoiceManager], depth=5, tries=100, seed=1234):
    successes = 0
    man = mang()
    list_of_sources = list(generate_lists(tries, seed))
    start_time = time.perf_counter()
    for l in list_of_sources:
        try:
            t = synth_type(man, ListRandomSource(l), EmptyContext(), d=5)
            if t:
                successes += 1
        except NoMoreBudget:
            pass
    time_consumed = time.perf_counter() - start_time
    print("Type", successes, tries, time_consumed)


def evaluate_term(
    mang: Callable[[], ChoiceManager],
    ty_name: str = "Int",
    depth=5,
    tries=100,
    seed=1234,
):
    successes = 0
    ty = parse_type(ty_name)
    man = mang()
    list_of_sources = list(generate_lists(tries, seed))
    start_time = time.perf_counter()
    for l in list_of_sources:
        man.reset()
        try:
            t = synth_term(man, ListRandomSource(l), EmptyContext(), ty, d=5)
            if t:
                man.reinforce()
                successes += 1
        except NoMoreBudget:
            pass
        except RecursionError:
            pass
        except Exception:
            print("Error at", l)
            pass
    time_consumed = time.perf_counter() - start_time
    print("Term", ty_name, successes, tries, time_consumed)
    if isinstance(man, DynamicProbManager):
        print(man.probabilities)


# evaluate_type(ChoiceManager, 5, 100)
# evaluate_type(DynamicProbManager, 5, 100)
# evaluate_term(ChoiceManager, "Int", 10, 1000, seed=987)
evaluate_term(DynamicProbManager, r"{x:Int | x > 3}", 10, 1000, seed=987)
evaluate_term(DepthAwareManager, r"{x:Int | x > 3}", 10, 1000, seed=987)
