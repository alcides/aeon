from __future__ import annotations

from typing import Any
from typing import Callable

from aeon.core.types import args_size_of_type
from aeon.core.types import Type
from aeon.synthesis.exceptions import NoMoreBudget
from aeon.synthesis.sources import RandomSource
from aeon.typing.context import EmptyContext
from aeon.typing.context import TypeBinder
from aeon.typing.context import TypingContext
from aeon.typing.context import VariableBinder
from aeon.typing.typeinfer import is_subtype

DEFAULT_BUDGET = 100


class ChoiceManager:
    debug: bool
    budget: int

    def __init__(self, default_budget=DEFAULT_BUDGET):
        self.debug = False
        self.default_budget = default_budget
        self.reset()

    def checkpoint(self):
        pass

    def reinforce(self):
        pass

    def reset(self):
        self.reset_budget()

    def reset_budget(self):
        self.budget = self.default_budget

    def choose_rule(
        self,
        r: RandomSource,
        options: list[Any],
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
                    + str(depth),
                )
            t = f()
            if t and validate(t):
                return t
            else:
                print("failed with ", f, "at", depth)
                self.undo_choice()
        raise NoMoreBudget()

    def make_choice(self, r: RandomSource, options: list[Any], depth: int):
        return options[0]

    def undo_choice(self):
        self.budget -= 1

    def allow_lit(self, ctx: TypingContext, ty: Type, d: int):
        return True

    def allow_var(self, ctx: TypingContext, ty: Type, d: int):
        return True

    def allow_app(self, ctx: TypingContext, ty: Type, d: int):
        return True

    def allow_abs(
        self,
        ctx: TypingContext,
        ty: Type,
        d: int,
        var_in_choices: bool,
        avoid_eta: bool,
    ):
        return True


class GrammaticalEvolutionManager(ChoiceManager):
    def make_choice(self, r: RandomSource, options: list[Any], depth: int):
        return r.choose(options)


def any_var_of_type(
    ctx: TypingContext,
    ty: Type,
    ictx: TypingContext | None = None,
) -> bool:
    if ictx is None:
        return any_var_of_type(ctx, ty, ctx)
    if isinstance(ictx, EmptyContext):
        return False
    elif isinstance(ictx, VariableBinder):
        if is_subtype(ctx, ictx.type, ty):
            return True
        return any_var_of_type(ctx, ty, ictx.prev)
    elif isinstance(ictx, TypeBinder):
        return any_var_of_type(ctx, ty, ictx.prev)
    assert False


def steps_necessary_to_close(ctx: TypingContext, ty: Type):
    max_arrows = max([0] + [args_size_of_type(ty_) for (_, ty_) in ctx.vars()])
    arrows_ty = args_size_of_type(ty)
    d = max(arrows_ty - max_arrows, 0)
    return d


class SemanticFilterManager(ChoiceManager):
    def allow_lit(self, ctx: TypingContext, ty: Type, d: int):
        return True

    def allow_var(self, ctx: TypingContext, ty: Type, d: int):
        return any_var_of_type(ctx, ty)

    def allow_app(self, ctx: TypingContext, ty: Type, d: int):
        return d > steps_necessary_to_close(ctx, ty) + 1

    def allow_abs(
        self,
        ctx: TypingContext,
        ty: Type,
        d: int,
        var_in_choices: bool,
        avoid_eta: bool,
    ):
        if avoid_eta:
            return not var_in_choices
        return True

    def make_choice(self, r: RandomSource, options: list[Any], depth: int):
        return r.choose(options)


class AdaptiveProbabilityManager(SemanticFilterManager):
    def __init__(self) -> None:
        self.probabilities: dict[str, int] = {}
        super().__init__()

    def make_choice(self, r: RandomSource, options: list[Any], depth: int):
        total = 0
        indices = []
        for o in options:
            key = self.make_key(o, depth)
            if key not in self.probabilities:
                self.probabilities[key] = 100
            total += self.probabilities[key]
            indices.append(total)

        chosen_index = r.next_integer() % total
        for index, opt in zip(indices, options):
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
            self.probabilities[o] = max(1, self.probabilities[o] * 0.9)

        if self.index_stack:
            index_to_remove_after = self.index_stack.pop()
            for _ in range(len(self.choices) - index_to_remove_after):
                k = self.choices.pop()
                undo(k)

    def reinforce(self):
        return
        for successful_choice in self.choices:
            self.probabilities[successful_choice] = self.probabilities[successful_choice] * 1.1

    def reset(self):
        super().reset()
        self.choices = []
        self.index_stack = []

    def make_key(self, fun, depth: int):
        return str(fun.__name__)


class DepthAwareAdaptiveManager(AdaptiveProbabilityManager):
    def make_key(self, fun, depth: int):
        return str(fun.__name__) + "_d_" + str(depth // 2)
