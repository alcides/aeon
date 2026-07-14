from __future__ import annotations

import argparse
import os
import sys
from argparse import ArgumentParser
from importlib.metadata import PackageNotFoundError, version
from pathlib import Path

from lark.exceptions import UnexpectedInput

from aeon.facade.api import (
    AeonError,
    ContractViolationError,
    CoreTypeCheckingError,
    ModuleNotFoundAeonError as AeonImportError,
    InstanceResolutionError,
    LinearityError,
    MethodResolutionError,
    NonOrderableComparisonError,
    UndecidableRefinementError,
    UnificationFailedError,
    UnificationKindError,
    UnificationSubtypingError,
    UnificationUnknownTypeError,
)
from aeon.facade.driver import AeonConfig, AeonDriver
from aeon.facade.exit_codes import ExitCode, error_exit_code
from aeon.sugar.lowering import LiquefactionException
from aeon.synthesis.api import SynthesisNotSuccessful, UnknownSynthesizerError
from aeon.logger.logger import export_log
from aeon.logger.logger import setup_logger
from aeon.lsp.server import AeonLanguageServer
from aeon.synthesis.uis.api import SynthesisUI, SynthesisFormat
from aeon.synthesis.uis.terminal import TerminalUI
from aeon.utils.pprint import pretty_print_sterm
from aeon.documentation import generate_documentation

sys.setrecursionlimit(10000)


def _package_version() -> str:
    try:
        return version("AeonLang")
    except PackageNotFoundError:
        return "unknown"


def parse_arguments():
    parser = argparse.ArgumentParser()

    if "-lsp" in sys.argv or "--language-server-mode" in sys.argv or "--version" in sys.argv:
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
    parser.add_argument(
        "--version",
        action="version",
        version=f"aeon {_package_version()}",
        help="show program's version number and exit",
    )
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
        "--strict-decidable",
        action="store_true",
        help=(
            "Treat refinements that leave the decidable fragment (nonlinear arithmetic such as `x * y`, "
            "division/modulo by a non-constant divisor, ...) as errors instead of warnings."
        ),
    )

    parser.add_argument(
        "--contracts",
        action="store_true",
        help="Check argument and result refinements at run time (gradual verification; off by default).",
    )

    parser.add_argument(
        "--test",
        action="store_true",
        help="Run property-based tests: check every @property function on random inputs",
    )

    parser.add_argument(
        "--seed",
        type=int,
        default=0,
        help="Random seed for property-based testing (--test). Generation is reproducible for a fixed seed.",
    )

    parser.add_argument(
        "-s",
        "--synthesizer",
        type=str,
        default="tdsyn_enumerative",
        help=(
            "Select a synthesizer: tdsyn_enumerative (default, type-directed BFS), tdsyn (same as tdsyn_enumerative), "
            "tdsyn_random (type-directed random walk), tactics (random tactic search), gp, synquid, "
            "random_search, enumerative (grammar enumeration), hc, 1p1, smt, "
            "sygus (reduce to SyGuS and solve with cvc5), decision_tree, llm (Ollama, default qwen2.5-coder:32b), "
            "llm_<model> (per-model Ollama backends, e.g. llm_qwen2.5-coder-14b), "
            "lta (Liquid Tree Automata, arXiv:2605.13456), "
            "fta (Finite Tree Automata, OOPSLA'17), "
            "afta (abstraction-refinement FTA, POPL'18), "
            "cata (constraint-annotated tree automata, recursive/relational), "
            "contata (cata version space, synthesises from @example I/O facts), "
            "symetric / xfta (metric program synthesis, arXiv:2206.06164)"
        ),
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

    parser.add_argument(
        "--export",
        type=str,
        default=None,
        metavar="FUN_NAME",
        help="Print a stand-alone, pure-Python version of the named function to stdout",
    )

    parser.add_argument(
        "--trust-report",
        action="store_true",
        help="Print the trusted computing base: the axioms and refined `native` bindings the program's guarantees rest on (none of which the type checker verifies).",
    )

    parser.add_argument(
        "--trust-for",
        type=str,
        default=None,
        metavar="FUN_NAME",
        help="Restrict --trust-report to the trusted assumptions transitively reachable from FUN_NAME.",
    )

    parser.add_argument(
        "--doc",
        action="store_true",
        help="Generate HTML documentation from the source file",
    )

    parser.add_argument(
        "--doc-output",
        type=str,
        default=None,
        help=(
            "Output path for the generated HTML doc. "
            "Either a file path (used as-is) or a directory path "
            "(the file is written there with the source's stem). "
            "Defaults to <source>.html next to the .ae file."
        ),
    )


def select_synthesis_ui() -> SynthesisUI:
    return TerminalUI()


def synthesis_requested(argv: list[str] | None = None) -> bool:
    """True when ``-s``/``--synthesizer`` or ``--budget`` was passed on the CLI."""
    if argv is None:
        argv = sys.argv[1:]
    for arg in argv:
        if arg in ("-s", "--synthesizer"):
            return True
        if arg == "--budget" or arg.startswith("--budget="):
            return True
    return False


def validate_synthesizer_or_exit(name: str) -> None:
    from aeon.synthesis.modules.synthesizerfactory import validate_synthesizer

    try:
        validate_synthesizer(name)
    except UnknownSynthesizerError as e:
        print(str(e), file=sys.stderr)
        sys.exit(ExitCode.OTHER_ERROR)


def format_location(err: AeonError) -> str:
    """Render an error's source span as ``file:line:col`` when positional
    information is available, otherwise fall back to ``str(location)``."""
    loc = err.position()
    file = getattr(loc, "file", "")
    start = getattr(loc, "start", None)
    if start is not None:
        line, col = start[0], start[1]
        prefix = f"{file}:" if file else ""
        return f"{prefix}{line}:{col}"
    return str(loc)


def _error_kind_and_hint(err: AeonError) -> tuple[str, str | None]:
    """Map each error variant to a short human-readable kind label and an
    optional hint suggesting how to fix it."""
    match err:
        case AeonImportError():
            return "Import error", "Check the module name and your AEONPATH / libraries folder."
        case UnificationSubtypingError():
            return "Type mismatch", "The expression's type is incompatible with the expected type."
        case UnificationFailedError():
            return "Unification error", "The same value is being constrained to two incompatible types."
        case UnificationKindError():
            return "Kind mismatch", "A type was used at the wrong kind."
        case UnificationUnknownTypeError():
            return "Unknown variable", "This name is not defined in the current context."
        case InstanceResolutionError():
            return "Missing instance", "Define a typeclass instance for this type, or add it as a constraint."
        case NonOrderableComparisonError():
            return "Non-orderable comparison", "Use Int, Float or String, or define an Ord instance for this type."
        case UndecidableRefinementError():
            return (
                "Undecidable refinement",
                "Keep refinements in the decidable fragment (linear arithmetic), or drop --strict-decidable.",
            )
        case MethodResolutionError():
            return "Method resolution error", "No method with this name is defined for the receiver's type."
        case LinearityError():
            return "Linearity error", "A binding's usage does not match its declared multiplicity."
        case ContractViolationError():
            return "Contract violation", "A runtime refinement check failed; see blame (caller vs callee)."
        case CoreTypeCheckingError():
            return "Type error", None
        case _:
            return "Error", None


def print_decidability_warnings(driver: AeonDriver) -> None:
    """Print non-fatal warnings for refinements that leave the decidable
    fragment (issue #438). Collected during ``driver.parse``; under
    ``--strict-decidable`` these surface as errors instead and this list is
    empty."""
    from aeon.verification.decidability import format_location

    if driver.cfg.strict_decidable:
        # Under strict mode these are reported as errors instead, so printing
        # them here as warnings too would just duplicate the diagnostic.
        return
    for w in getattr(driver, "decidability_warnings", []):
        print(f">>> Warning ({w.construct}) at {format_location(w.location)}:", file=sys.stderr)
        print(f"    {w.message}", file=sys.stderr)


def handle_error(err: AeonError):
    kind, hint = _error_kind_and_hint(err)
    print(f">>> {kind} at {format_location(err)}:")
    print(f"    {err}")
    if hint is not None:
        print(f"    hint: {hint}")


def main() -> None:
    args = parse_arguments()

    logger = setup_logger()
    logfile_name = None
    match getattr(args, "filename", None), getattr(args, "language_server_mode", None):
        case (str() as fn, _):
            logfile_name = fn
        case (_, True):
            logfile_name = "lsp"
        case _:
            logfile_name = None
    export_log(args.log, args.logfile, logfile_name)

    if args.debug:
        logger.add(sys.stderr)
    if args.timings:
        logger.add(sys.stderr, level="TIME")

    run_tests = getattr(args, "test", False)
    if run_tests and args.no_main:
        print("warning: --no-main is ignored under --test (a main slot is needed to evaluate properties).")
    cfg = AeonConfig(
        synthesizer=args.synthesizer,
        synthesis_ui=select_synthesis_ui(),
        synthesis_budget=args.budget,
        timings=args.timings,
        # ``--export`` forces ``no_main`` (no synthesis hole in main), but
        # property evaluation splices the call into the program's main slot, so
        # under ``--test`` the slot must exist even if ``--no-main`` was passed.
        no_main=(args.no_main or bool(getattr(args, "export", None))) and not run_tests,
        synthesis_format=SynthesisFormat.from_string(args.synthesis_format),
        strict_decidable=getattr(args, "strict_decidable", False),
        contracts=getattr(args, "contracts", False),
    )
    driver = AeonDriver(cfg)

    if synthesis_requested():
        validate_synthesizer_or_exit(args.synthesizer)

    if hasattr(args, "language_server_mode"):
        aeon_lsp = AeonLanguageServer(driver)
        aeon_lsp.start(args.tcp)
        sys.exit(0)

    if hasattr(args, "doc") and args.doc:
        source_path = Path(args.filename)
        if args.doc_output:
            target = Path(args.doc_output)
            if target.is_dir() or args.doc_output.endswith(("/", os.sep)):
                output_path = str(target / f"{source_path.stem}.html")
            else:
                output_path = str(target)
        else:
            output_path = str(source_path.with_suffix(".html"))
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        generate_documentation(args.filename, output_path)
        print(f"Documentation generated: {output_path}")
        sys.exit(0)

    try:
        errors = driver.parse(args.filename)
    except UnexpectedInput as e:
        # Lark's parse errors carry their own position rendering.
        print(">>> Syntax error:")
        print(f"    {e}")
        sys.exit(ExitCode.SYNTAX_ERROR)
    except LiquefactionException as e:
        print(">>> Invalid refinement predicate:")
        print(f"    {e}")
        print("    hint: refinement predicates are restricted to liquid terms (no method calls or binders).")
        sys.exit(ExitCode.INVALID_REFINEMENT)
    except NameError as e:
        # Name-resolution failures (e.g. ``Module.unknown``) surface as NameError.
        print(">>> Unknown name:")
        print(f"    {e}")
        sys.exit(ExitCode.UNKNOWN_NAME)
    except AeonError as e:
        handle_error(e)
        sys.exit(error_exit_code(e))

    print_decidability_warnings(driver)

    match errors:
        case [] if getattr(args, "trust_report", False) or getattr(args, "trust_for", None):
            print(driver.trust_report(filename=args.filename, for_func=args.trust_for))
        case [] if args.export:
            from aeon.backend.python_export import PythonExportError

            try:
                print(driver.export(args.export))
            except SynthesisNotSuccessful:
                print(f"Cannot find a suitable expression within {args.budget} seconds.", file=sys.stderr)
                sys.exit(2)
            except PythonExportError as e:
                print(f">>> Export error: {e}", file=sys.stderr)
                sys.exit(2)
        case []:
            if run_tests:
                if not driver.has_tests():
                    print("No @property functions found.")
                    sys.exit(0)
                failures = driver.run_tests(seed=args.seed)
                sys.exit(ExitCode.TESTS_FAILED_OR_CRASH if failures else ExitCode.SUCCESS)
            if synthesis_requested() and not driver.has_synth():
                print("No holes to synthesize.", file=sys.stderr)
                sys.exit(ExitCode.SYNTHESIS_NOT_SUCCESSFUL)
            match (args.format, driver.has_synth()):
                case (True, _):
                    driver.pretty_print(args.filename, args.fix)
                case (False, True):
                    validate_synthesizer_or_exit(args.synthesizer)
                    try:
                        term = driver.synth()
                    except SynthesisNotSuccessful as e:
                        message = str(e) or f"Cannot find a suitable expression within {args.budget} seconds."
                        print(message, file=sys.stderr)
                        sys.exit(ExitCode.SYNTHESIS_NOT_SUCCESSFUL)
                    print("Synthesized:")
                    print("#str")
                    print(str(term))
                    print("#pprint")
                    print(pretty_print_sterm(term))
                case (False, False):
                    try:
                        driver.run()
                    except ContractViolationError as contract_err:
                        handle_error(contract_err)
                        sys.exit(error_exit_code(contract_err))
        case [first, *_]:
            for err in errors:
                handle_error(err)
            sys.exit(error_exit_code(first))


if __name__ == "__main__":
    main()
