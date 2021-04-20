import pathlib
import sys
import random
import time
from typing import Any, Callable, List
from statistics import mean
import typing

experiments_folder = pathlib.Path(__file__).parent
sys.path.append(str(experiments_folder.parent.absolute()))


import zstandard as zstd

from aeon.synthesis.exceptions import NoMoreBudget
from aeon.typing.context import EmptyContext, VariableBinder
from aeon.synthesis.sources import ListRandomSource
from aeon.frontend.parser import parse_term, parse_type
from aeon.synthesis.term_synthesis import synth_term
from aeon.synthesis.type_synthesis import synth_type
from aeon.core.distance import pairwise_distance, term_depth
from aeon.core.types import t_int, t_bool
from aeon.synthesis.choice_manager import (
    DepthAwareManager,
    DynamicProbManager,
    ChoiceManager,
)
from aeon.prelude.prelude import typing_vars
from aeon.utils.ctx_helpers import build_context

type_tries = 100
term_tries = 100


compressor = zstd.ZstdCompressor(
    level=22, write_checksum=False, write_content_size=False, write_dict_id=False
)


def entropy(l: List[Any]) -> float:
    s = " | ".join([str(x) for x in l])
    compressed = compressor.compress(s.encode("ascii"))
    return len(compressed)


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


base_ctx = build_context(
    {
        "plus": parse_type(r"(x:Int) -> (y:Int) -> {z:Int | z == (x + y) }"),
        "minus": parse_type(r"(x:Int) -> (y:Int) -> {z:Int | z == (x - y) }"),
        "times": parse_type(r"(x:Int) -> (y:Int) -> {z:Int | z == (x * y) }"),
        "div": parse_type(r"(x:Int) -> (y:Int) -> {z:Int | z == (x / y) }"),
        "abs": parse_type(
            r"(x:Int) -> (y:Int) -> {z:Int | (z == x && x > y) || (z == y && y >= x) }"
        ),
        "not": parse_type("(x:Bool) -> Bool"),
        "eqInt": parse_type("(x:Int) -> (y:Int) -> Int"),
        "eqBool": parse_type("(x:Bool) -> (y:Bool) -> Bool"),
        "and": parse_type("(x:Bool) -> (y:Bool) -> Bool"),
        "or": parse_type("(x:Bool) -> (y:Bool) -> Bool"),
        "gt": parse_type("(x:Int) -> (y:Int) -> Bool"),
        "gte": parse_type("(x:Int) -> (y:Int) -> Bool"),
        "lt": parse_type("(x:Int) -> (y:Int) -> Bool"),
        "lte": parse_type("(x:Int) -> (y:Int) -> Bool"),
        "isPositive": parse_type("(x:Int) -> Bool"),
        "isNegative": parse_type("(x:Int) -> Bool"),
        "toInt": parse_type("(x:Bool) -> Int"),
    }
)
for i in range(35):
    name = f"x_{i}"
    base_ctx = VariableBinder(base_ctx, name, t_int)
for i in range(8):
    name = f"b_{i}"
    base_ctx = VariableBinder(base_ctx, name, t_bool)


def evaluate_term(
    mang: Callable[[], ChoiceManager],
    ty_name: str = "Int",
    depth=5,
    tries=100,
    seed=1234,
):
    successes = []
    ty = parse_type(ty_name)
    man = mang()
    list_of_sources = list(generate_lists(tries, seed))
    start_time = time.perf_counter()
    for l in list_of_sources:
        man.reset()
        try:
            t = synth_term(man, ListRandomSource(l), base_ctx, ty, d=depth)
            if t:
                print(t)
                man.reinforce()
                successes.append(t)
            else:
                print(":(")
        except NoMoreBudget as e:
            pass
            print("fb")
        except RecursionError:
            pass
        except Exception as e:
            print("Error at", e)
            pass
    time_consumed = time.perf_counter() - start_time
    ctreeedit = pairwise_distance(successes)
    csuccesses = len(successes)
    centropy = entropy(successes)
    if successes:
        avgdepth = mean([term_depth(t) for t in successes])
        maxdepth = max([term_depth(t) for t in successes])
    else:
        avgdepth = 0
        maxdepth = 0
    print(
        f"Experiment;{mang.__name__};{tries};{ty_name};{depth};{seed};{csuccesses};{time_consumed};{centropy};{ctreeedit};{avgdepth};{maxdepth}",
    )
    # print(successes)
    # if isinstance(man, DynamicProbManager):
    #    print(man.probabilities)


total_tries = 10


for manc in [DynamicProbManager, DepthAwareManager, ChoiceManager]:
    for t in [
        "Int",
        r"{x: Int | x > 0}",
        # r"{x: Int | x > 0 && x < 1000}",
        # r"{x: Int | x > 0 && x < 100}",
        # r"{x: Int | x == 3 && x == 5}",
    ]:
        for d in [10]:  # [3, 5, 10, 20, 30, 50]:
            for seed in range(1):
                evaluate_term(manc, t, d, total_tries, seed=seed)
