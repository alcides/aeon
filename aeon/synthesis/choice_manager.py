from typing import Any, Callable, Dict, List

from aeon.synthesis.sources import RandomSource
from aeon.synthesis.exceptions import NoMoreBudget


MAX_TRIES = 128


class ChoiceManager(object):
    def choose_rule(
        self,
        r: RandomSource,
        options: List[Any],
        depth: int,
        budget: int = MAX_TRIES,
        validate: Callable[[Any], bool] = lambda x: True,
    ):
        for t in range(budget):
            f = self.make_choice(r, options, depth)
            print(
                "Made choice, "
                + str(f.__name__)
                + ", from: "
                + str([str(f.__name__) for f in options])
                + " at "
                + str(depth)
            )
            t = f()
            if t and validate(t):
                return t
            else:
                print("failed with ", f, "at", depth)
                self.undo_choice()
        raise NoMoreBudget()

    def make_choice(
        self, r: RandomSource, options: List[Any], depth: int
    ):  # TODO: PRIORITY - whether each option is terminal or not
        return r.choose(options)

    def undo_choice(self):
        pass

    def checkpoint(self):
        pass

    def reinforce(self):
        pass

    def reset(self):
        pass


class DynamicProbManager(ChoiceManager):
    def __init__(self) -> None:
        self.probabilities: Dict[str, int] = {}
        self.reset()

    def make_choice(self, r: RandomSource, options: List[Any], depth: int):
        total = 0
        indices = []
        for o in options:
            key = self.make_key(o, depth)
            if key not in self.probabilities:
                self.probabilities[key] = 100
            total += self.probabilities[key]
            indices.append(total)

        chosen_index = r.next_integer() % total
        for (index, opt) in zip(indices, options):
            if chosen_index < index:
                key = self.make_key(o, depth)
                self.choices.append(key)
                return opt
        assert False

    def checkpoint(self):
        self.index_stack.append(len(self.choices))

    def undo_choice(self):
        def undo(o):
            self.probabilities[o] = max(1, int(self.probabilities[o] * 0.9))

        if self.index_stack:
            index_to_remove_after = self.index_stack.pop()
            for _ in range(len(self.choices) - index_to_remove_after):
                k = self.choices.pop()
                undo(k)

    def reinforce(self):
        return
        for successful_choice in self.choices:
            self.probabilities[successful_choice] = int(
                self.probabilities[successful_choice] * 1.1
            )

    def reset(self):
        self.choices: List[Any] = []
        self.index_stack: List[int] = []

    def make_key(self, fun, depth: int):
        return str(fun.__name__)


class DepthAwareManager(DynamicProbManager):
    def make_key(self, fun, depth: int):
        return str(fun.__name__) + "_d_" + str(depth // 5)
