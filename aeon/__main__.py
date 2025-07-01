from __future__ import annotations

import os
import sys
import argparse

from aeon.facade.api import AeonError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.synthesis.uis.api import SynthesisUI
from aeon.synthesis.uis.ncurses import NCursesUI
from aeon.synthesis.uis.terminal import TerminalUI


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


def read_file(filename: str) -> str:
    with open(filename) as file:
        return file.read()


def log_type_errors(errors: list[Exception | str]):
    print("TYPECHECKER", "-------------------------------")
    print("TYPECHECKER", "+     Type Checking Error     +")
    for error in errors:
        print("TYPECHECKER", "-------------------------------")
        print("TYPECHECKER", error)
    print("TYPECHECKER", "-------------------------------")


def select_synthesis_ui() -> SynthesisUI:
    if os.environ.get("TERM", None):
        return NCursesUI()
    else:
        return TerminalUI()


def handle_error(err: AeonError):
    # TODO: handle each error with proper printing
    match err:
        case _:
            print(f">>> Error at {err.position()}:")
            print(err)


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
    driver = AeonDriver(cfg)

    if args.core:
        errors = driver.parse_core(args.filename)
    else:
        errors = driver.parse(args.filename)

    if errors:
        for err in errors:
            handle_error(err)
    elif driver.has_synth():
        term = driver.synth()
        print("Synthesized:")
        print(term)
    else:
        driver.run()


if __name__ == "__main__":
    main()
