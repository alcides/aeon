from __future__ import annotations

import argparse

from geneticengine.core.grammar import Grammar
from geneticengine.core.representations.tree.treebased import TreeBasedRepresentation

from aeon.backend.evaluator import eval
from aeon.backend.evaluator import EvaluationContext
from aeon.core.types import top
from aeon.frontend.parser import parse_term
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.prelude.prelude import evaluation_vars
from aeon.prelude.prelude import typing_vars
from aeon.sugar.desugar import desugar
from aeon.sugar.parser import parse_program
from aeon.sugar.program import Program
from aeon.synthesis_grammar.fitness import get_minimize
from aeon.synthesis_grammar.synthesizer import Synthesizer
from aeon.typechecking.typeinfer import check_and_log_type_errors
from aeon.utils.ctx_helpers import build_context


def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("filename", help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument(
        "-l",
        "--log",
        nargs="+",
        default="",
        help="set log level: \nTRACE \nDEBUG \nINFO \nTYPECHECKER \nCONSTRAINT " "\nWARNINGS \nERROR \nCRITICAL",
    )
    parser.add_argument("-f", "--logfile", action="store_true", help="export log file")
    return parser.parse_args()


def read_file(filename: str) -> str:
    with open(filename) as file:
        return file.read()


def process_code(core: bool, code: str) -> tuple:
    if core:
        context = build_context(typing_vars)
        evaluation_ctx = EvaluationContext(evaluation_vars)
        return parse_term(code), context, evaluation_ctx, None
    else:
        prog: Program = parse_program(code)
        return desugar(prog)


def synthesize_solution(
    synthesizer: Synthesizer,
    file_path: str,
    grammar: Grammar,
    minimize: bool | list[bool],
    **kwargs,
):
    return synthesizer.synthesize(
        file_path=file_path,
        grammar=grammar,
        representation=TreeBasedRepresentation,
        minimize=minimize,
        **kwargs,
    )


if __name__ == "__main__":

    args = parse_arguments()
    logger = setup_logger()
    export_log(args.log, args.logfile, args.filename)

    aeon_code = read_file(args.filename)
    p, ctx, ectx, minimize_flag = process_code(args.core, aeon_code)
    logger.info(p)

    if not check_and_log_type_errors(ctx, p, top):
        synthesizer = Synthesizer(ctx, p, top, ectx)

        if len(synthesizer.holes) <= 1:
            eval(p, ectx)
            exit()

        grammar = synthesizer.get_grammar()

        minimize = get_minimize(minimize_flag) if minimize_flag else True

        common_synthesize_args = {
            "max_depth": 8,
            "population_size": 20,
            "n_elites": 1,
            "target_fitness": 0,
            "timer_stop_criteria": True,
            "timer_limit": 60,
        }

        best_solution = synthesize_solution(synthesizer, args.filename, grammar, minimize, **common_synthesize_args)

        print(f"Best solution: {best_solution.genotype}")
