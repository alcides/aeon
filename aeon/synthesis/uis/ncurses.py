from typing import Any
from aeon.backend.evaluator import EvaluationContext
from aeon.core.terms import Term
from aeon.core.types import Type
from aeon.synthesis.api import SynthesisUI
from aeon.typechecking.context import TypingContext

import curses


class NCursesUI(SynthesisUI):

    def start(
        self,
        typing_ctx: TypingContext,
        evaluation_ctx: EvaluationContext,
        target_name: str,
        target_type: Type,
        budget: Any,
    ):
        self.stdscr = curses.initscr()
        self.target_name = target_name
        self.target_type = target_type
        self.budget = budget

    def register(self, solution: Term, quality: Any, elapsed_time: float,
                 is_best: bool):
        if is_best:
            self.best_solution = solution
            self.best_quality = quality

        self.stdscr.clear()
        self.stdscr.addstr(0, 0, f"Synthesizing ?{self.target_name}")
        self.stdscr.addstr(1, 0, "====================================")
        self.stdscr.addstr(3, 0, f"Fitness: {quality}")
        self.stdscr.addstr(4, 0, f"Program: {solution}")
        self.stdscr.addstr(6, 0, f"Best: {self.best_solution}")
        self.stdscr.addstr(7, 0, f"Best Fitness: {self.best_quality}")
        self.stdscr.addstr(9, 0, "====================================")
        self.stdscr.addstr(10, 0,
                           f"""{elapsed_time:.1f} / {self.budget:.1f}s""")

        self.stdscr.refresh()

    def end(self, solution: Term, quality: Any):
        curses.endwin()

    def wrapper(self, f):
        return curses.wrapper(f)
