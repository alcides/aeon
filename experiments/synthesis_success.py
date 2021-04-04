import pathlib
import sys
import random

experiments_folder = pathlib.Path(__file__).parent
sys.path.append(str(experiments_folder.parent.absolute()))

from aeon.synthesis.exceptions import NoMoreBudget
from aeon.typing.context import EmptyContext
from aeon.synthesis.sources import ListRandomSource
from aeon.frontend.parser import parse_term, parse_type
from aeon.synthesis.term_synthesis import synth_term

ty = parse_type("Int")

r = random.Random(1234)


def generate_lists(n):
    for _ in range(n):
        size = r.randint(0, 50)
        yield [r.randint(-256, 256) for _ in range(size)]


successes = 0
for l in generate_lists(100):
    try:
        t = synth_term(ListRandomSource(l), EmptyContext(), ty, 5)
        successes += 1
    except NoMoreBudget:
        pass
print(successes)
