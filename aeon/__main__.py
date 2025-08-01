from __future__ import annotations

import argparse
import sys
from argparse import ArgumentParser

from aeon.facade.api import AeonError
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.lsp.server import AeonLanguageServer
from aeon.synthesis.uis.api import SynthesisUI, SynthesisFormat
from aeon.synthesis.uis.terminal import TerminalUI
from aeon.utils.pprint import pretty_print_sterm

sys.setrecursionlimit(10000)


def parse_arguments():
    parser = argparse.ArgumentParser()

    if "-lsp" in sys.argv or "--language-server-mode" in sys.argv:
        parser.add_argument(
            "-lsp",
            "--language-server-mode",
            action="store_true",
            help="run language server mode",
        )
        parser.add_argument(
            "--tcp",
            help="listen on tcp port or hostname:port on IPv4.",
            type=str,
        )

    else:
        parser.add_argument("filename", help="name of the aeon files to be synthesized")

    _parse_common_arguments(parser)
    return parser.parse_args()


def _parse_common_arguments(parser: ArgumentParser):
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

    parser.add_argument(
        "-s",
        "--synthesizer",
        type=str,
        default="gp",
        help="Select a synthesizer for synthesis(gp for Genetic programming(Defaut), synquid for Synquid, random_search for Random Search, enumerative for Enumerative Search, hc for Hill Climbing, and 1p1 for One Plus One)",
    )

    parser.add_argument(
        "--synthesis-format",
        type=str,
        choices=["default", "json"],
        default="default",
        help="Select the synthesised holes format results: default or json",
    )

    parser.add_argument(
        "--format",
        action="store_true",
        help="Prints a pretty print version of the code to the stdout",
    )

    parser.add_argument(
        "--fix",
        action="store_true",
        help="Uses a pretty print version of the code to reformat it",
    )

    return parser.parse_args()


def select_synthesis_ui() -> SynthesisUI:
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
    logfile_name = None
    if hasattr(args, "filename"):
        logfile_name = args.filename
    elif hasattr(args, "language_server_mode"):
        logfile_name = "lsp"
    export_log(args.log, args.logfile, logfile_name)

    if args.debug:
        logger.add(sys.stderr)
    if args.timings:
        logger.add(sys.stderr, level="TIME")

    cfg = AeonConfig(
        synthesizer=args.synthesizer,
        synthesis_ui=select_synthesis_ui(),
        synthesis_budget=args.budget,
        timings=args.timings,
        no_main=args.no_main,
        synthesis_format=SynthesisFormat.from_string(args.format),
    )
    driver = AeonDriver(cfg)

    if hasattr(args, "language_server_mode"):
        aeon_lsp = AeonLanguageServer(driver)
        aeon_lsp.start(args.tcp)
        sys.exit(0)

    if args.core:
        errors = driver.parse_core(args.filename)
    else:
        errors = driver.parse(args.filename)

    if errors:
        for err in errors:
            handle_error(err)
    elif args.format:
        driver.pretty_print(args.filename, args.fix)

    elif driver.has_synth():
        term = driver.synth()
        print("Synthesized:")
        print("#str")
        print(str(term))
        print("#pprint")
        print(pretty_print_sterm(term))
    else:
        driver.run()


if __name__ == "__main__":
    main()
