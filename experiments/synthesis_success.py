from __future__ import annotations

import os
import os.path as path
import pathlib
import random
import sys
import time
from optparse import OptionParser
from statistics import mean
from typing import Any
from typing import Callable


import zstandard as zstd

from aeon.synthesis.exceptions import NoMoreBudget
from aeon.typechecking.context import EmptyContext, VariableBinder
from aeon.synthesis.sources import ListRandomSource
from aeon.frontend.parser import parse_type
from aeon.synthesis.term_synthesis import synth_term
from aeon.synthesis.type_synthesis import synth_type
from aeon.core.distance import pairwise_distance, term_depth
from aeon.core.types import t_int, t_bool
from aeon.synthesis.choice_manager import (
    AdaptiveProbabilityManager,
    DepthAwareAdaptiveManager,
    ChoiceManager,
    GrammaticalEvolutionManager,
    SemanticFilterManager,
)
from aeon.utils.ctx_helpers import build_context

experiments_folder = pathlib.Path(__file__).parent
sys.path.append(str(experiments_folder.parent.absolute()))

type_tries = 100

compressor = zstd.ZstdCompressor(
    level=22,
    write_checksum=False,
    write_content_size=False,
    write_dict_id=False,
)


def save_line(str):
    with open(fname, "a") as f:
        f.write(str + "\n")


def entropy(l: list[Any]) -> float:
    s = " | ".join([str(x) for x in l])
    compressed = compressor.compress(s.encode("ascii"))
    return len(compressed)


def generate_lists(n, seed=1234):
    r = random.Random(seed)
    for _ in range(n):
        size = r.randint(10, 100)
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
            r"(x:Int) -> (y:Int) -> {z:Int | (z == x) && (x > y) || (z == y) && (y >= x) }",
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
    },
)
for i in range(2):
    name = f"x_{i}"
    base_ctx = VariableBinder(base_ctx, name, t_int)
for i in range(2):
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
    for i, l in enumerate(list_of_sources):
        man.reset()
        try:
            t = synth_term(man, ListRandomSource(l), base_ctx, ty, d=depth)
            if t:
                # print(t)
                man.reinforce()
                successes.append(t)
            else:
                print(":(")
        except NoMoreBudget:
            print("out of budget", i)
            continue
        except RecursionError:
            continue
        except Exception as e:
            print("Error at", e)
            raise e
    time_consumed = time.perf_counter() - start_time
    print("Computing stats...")
    ctreeedit = pairwise_distance(successes)
    csuccesses = len(successes)
    centropy = entropy(successes)
    if successes:
        avgdepth = mean([term_depth(t) for t in successes])
        maxdepth = max(term_depth(t) for t in successes)
    else:
        avgdepth = 0
        maxdepth = 0
    save_line(
        f"{mang.__name__};{tries};{ty_name};{depth};{seed};{csuccesses};{time_consumed};{centropy};{ctreeedit};{avgdepth};{maxdepth}",
    )
    print("Stats done")
    # print(successes)
    # if isinstance(man, GrammaticalEvolutionManager):
    #    print(man.probabilities)


parser = OptionParser()
parser.add_option(
    "-d",
    "--depth",
    dest="depth",
    type="int",
    help="Maximum allowed depth",
    metavar="DEPTH",
    default=6,
)
parser.add_option(
    "-s",
    "--seed",
    dest="seed",
    type="int",
    help="Seed for RNG",
    metavar="SEED",
    default=0,
)
parser.add_option(
    "-t",
    "--type",
    dest="type",
    help="Type to synthesize",
    metavar="TYPE",
)
parser.add_option(
    "-n",
    "--typename",
    dest="typename",
    help="Name of the type",
    metavar="TYPENAME",
)
parser.add_option(
    "-r",
    "--totaltries",
    dest="totaltries",
    type="int",
    help="Total Number of Tries",
    metavar="TOTALTRIES",
)

parser.add_option(
    "-m",
    "--manager",
    dest="manager",
    help="Class to use as ChoiceManager. One of GrammaticalEvolution, SemanticFilter, Adaptive, DepthAwareAdaptive",
    metavar="MANAGER",
)

(options, args) = parser.parse_args()
filename = f"ty_{options.typename}_depth_{options.depth}_totaltries_{options.totaltries}_mode_{options.manager}_seed_{options.seed}"
print(filename)
print(options)

fname = str(experiments_folder / f"{filename}.csv")
ename = str(experiments_folder / f"{filename}.err")

with open(fname, "w") as f:
    f.truncate(0)

if path.exists(ename):
    os.remove(ename)

classnames = {
    "GrammaticalEvolution": GrammaticalEvolutionManager,
    "SemanticFilter": SemanticFilterManager,
    "Adaptive": AdaptiveProbabilityManager,
    "DepthAwareAdaptive": DepthAwareAdaptiveManager,
}

manc = classnames[options.manager]

try:
    evaluate_term(
        manc,
        ty_name=options.type,
        depth=options.depth,
        tries=options.totaltries,
        seed=options.seed,
    )
except Exception as e:
    raise e
    import traceback

    with open(ename, "a") as f:
        f.write(str(e))
        f.write("\n")
        f.write(traceback.format_exc())
        f.write("\n")
        f.write(f"error on {i}\n")

[
    # "Int",
    r"{x: Int | x > 0}",
    r"{x: Int | x > 0 && x < 1000}",
    r"{x: Int | x > 0 && x < 100}",
    r"{x: Int | x == 3 && x == 5}",
]
