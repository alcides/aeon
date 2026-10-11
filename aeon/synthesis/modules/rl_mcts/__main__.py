"""Generate SyGuS tasks and train local policy/value checkpoints from valid LIA."""

from __future__ import annotations

import argparse
from collections.abc import Callable
from functools import partial
from pathlib import Path
from typing import Any

import z3

from aeon.synthesis.modules.rl_mcts.dataset import generate_problems, solve_generated
from aeon.synthesis.modules.rl_mcts.learning import train
from aeon.synthesis.modules.rl_mcts.features import Syntax
from aeon.synthesis.modules.rl_mcts.search import Guidance, SearchConfig, SearchResult


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("generate", "train", "train-aeon"))
    parser.add_argument(
        "sources", nargs="+", type=Path, help="valid SMT-LIB formulas, or single-hole .ae files with train-aeon"
    )
    parser.add_argument("--output", type=Path, required=True, help="dataset directory or model checkpoint directory")
    parser.add_argument("--iterations", type=int, default=2)
    parser.add_argument("--budget", type=float, default=10)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--limit", type=int, default=8, help="maximum generated tasks per source")
    parser.add_argument("--rollouts", type=int, default=6500)
    parser.add_argument("--bins", type=int, default=4093, help="feature hash base")
    args = parser.parse_args()
    config = SearchConfig(rollouts=args.rollouts)
    callbacks: list[Callable[[Guidance | None], tuple[Syntax, SearchResult[Any]]]] = []
    if args.mode == "train-aeon":
        from aeon.synthesis.modules.rl_mcts.training import aeon_problem

        callbacks = [aeon_problem(s, budget=args.budget, seed=args.seed, config=config) for s in args.sources]
        model, replays = train(callbacks, iterations=args.iterations, bins=args.bins, seed=args.seed)
        model.save(args.output)
        print(f"Trained {len(replays)} iterations on {len(callbacks)} Aeon tasks; saved {args.output}")
        return
    problems = []
    for source in args.sources:
        formula = z3.And(*z3.parse_smt2_file(str(source)))
        problems.extend(generate_problems(formula, limit=args.limit))
    if not problems:
        parser.error("no nontrivial training tasks could be generated from these sources")
    if args.mode == "generate":
        args.output.mkdir(parents=True, exist_ok=True)
        for index, problem in enumerate(problems):
            (args.output / f"problem-{index:04}.sl").write_text(problem.to_sygus(), encoding="utf-8")
        print(f"Generated {len(problems)} witness-validated SyGuS tasks")
        return
    callbacks = [partial(solve_generated, p, config=config, budget=args.budget, seed=args.seed) for p in problems]
    model, replays = train(callbacks, iterations=args.iterations, bins=args.bins, seed=args.seed)
    model.save(args.output)
    print(f"Trained {len(replays)} iterations on {len(problems)} tasks; saved {args.output}")


if __name__ == "__main__":
    main()
