from __future__ import annotations

import os
import sys
import argparse

from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.uis.ncurses import NCursesUI
from aeon.synthesis.uis.terminal import TerminalUI

from aeon.facade import AeonConfig, AeonDriver, AeonError, CompilerFeedback
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger

sys.setrecursionlimit(10000)


def parse_arguments():
    parser = argparse.ArgumentParser()

    parser.add_argument("filename", help="name of the aeon files to be synthesized")
    parser.add_argument("--core", action="store_true", help="synthesize a aeon core file")
    parser.add_argument("--budget", type=int, default=60, help="Time for synthesis (in seconds).")
    parser.add_argument(
        "-l",
        "--log",
        nargs="+",
        default="",
        help="""set log level: \nTRACE \nDEBUG \nINFO \nWARNINGS \nCONSTRAINT \nTYPECHECKER \nSYNTH_TYPE \nCONSTRAINT \nSYNTHESIZER
                \nERROR \nCRITICAL\n TIME""",
    )
    parser.add_argument(
        "-f",
        "--logfile",
        action="store_true",
        help="export log file",
    )
    parser.add_argument(
        "-d",
        "--debug",
        action="store_true",
        help="Show debug information",
    )

    parser.add_argument(
        "-t",
        "--timings",
        action="store_true",
        help="Show timing information",
    )

    parser.add_argument("-n", "--no-main", action="store_true", help="Disables introducing hole in main")

    return parser.parse_args()


def select_synthesis_ui() -> SynthesisUI:
    if os.environ.get("TERM", None):
        return NCursesUI()
    else:
        return TerminalUI()


class CLIFeedback(CompilerFeedback):
    def handle_error(self, e: AeonError):
        print(e)


def main() -> None:
    args = parse_arguments()

    logger = setup_logger()
    export_log(args.log, args.logfile, args.filename)
    if args.debug:
        logger.add(sys.stderr)
    if args.timings:
        logger.add(sys.stderr, level="TIME")

    cfg = AeonConfig(
        synthesis_ui=select_synthesis_ui(), synthesis_budget=args.budget, timings=args.timings, no_main=args.no_main
    )
    feedback = CLIFeedback()
    driver = AeonDriver(cfg, feedback)

    if args.core:
        errors = driver.parse_core(args.filename)
    else:
        errors = driver.parse(args.filename)
    if errors:
        for e in errors:
            feedback.handle_error(e)

    if driver.has_synth():
        driver.synth()
    else:
        driver.run()


if __name__ == "__main__":
    main()
