from typing import Any, Callable, Dict, List

from aeon.synthesis.sources import RandomSource
from aeon.synthesis.exceptions import NoMoreBudget


DEFAULT_BUDGET = 100


class ChoiceManager(object):
    debug: bool
    budget: int

    def __init__(self):
        self.debug = False
        self.reset_budget()

    def choose_rule(
        self,
        r: RandomSource,
        options: List[Any],
        depth: int,
        validate: Callable[[Any], bool] = lambda x: True,
    ):
        while self.budget > 0:
            f = self.make_choice(r, options, depth)
            if self.debug:
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
        self.budget -= 1

    def checkpoint(self):
        pass

    def reinforce(self):
        pass

    def reset(self):
        self.reset_budget()

    def reset_budget(self):
        self.budget = DEFAULT_BUDGET


class DynamicProbManager(ChoiceManager):
    def __init__(self) -> None:
        super().__init__()
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
        super().undo_choice()

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
        super().reset()
        self.choices: List[Any] = []
        self.index_stack: List[int] = []

    def make_key(self, fun, depth: int):
        return str(fun.__name__)


class DepthAwareManager(DynamicProbManager):
    def make_key(self, fun, depth: int):
        return str(fun.__name__) + "_d_" + str(depth // 2)
