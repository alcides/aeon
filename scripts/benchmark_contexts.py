"""Compare indexed bindings with baseline using fresh processes and full validation."""

from __future__ import annotations

import argparse
import gc
import hashlib
import importlib.abc
import importlib.util
import json
import math
import os
from pathlib import Path
import random
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
VARIANTS = ("baseline", "indexed")
CASES = ("list_20_bounded", "array_int_fit", "image_key", "knapsack_50")
BASELINE = "bc63fc6c709087031bf5dc68129b2670e56db685"


class BaselineModules(importlib.abc.MetaPathFinder, importlib.abc.Loader):
    """Load selected baseline modules before any compiler import, without editing files."""

    def __init__(self, variant, revision):
        paths = []
        if variant == "baseline":
            paths += ["aeon/typechecking/context.py", "aeon/utils/name.py"]
        self.sources = {}
        for path in paths:
            source = subprocess.check_output(["git", "show", f"{revision}:{path}"], cwd=ROOT, text=True)
            if path.endswith("typechecking/context.py"):
                # Keep the previous direct-reverse-iteration improvement in
                # both variants, isolating the binding-index optimization.
                source += "\ndef _direct_reverse(self):\n    if self._mutable is not None:\n        return reversed(self._mutable)\n    return chain(reversed(self._tail), chain.from_iterable(map(reversed, reversed(self._blocks))))\n_ContextSnapshot.__reversed__ = _direct_reverse\n"
            self.sources[path[:-3].replace("/", ".")] = source

    def find_spec(self, fullname, path=None, target=None):
        return importlib.util.spec_from_loader(fullname, self) if fullname in self.sources else None

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        filename = str(ROOT / (module.__name__.replace(".", "/") + ".py"))
        module.__file__ = filename
        exec(compile(self.sources[module.__name__], filename, "exec"), module.__dict__)


def verify(args):
    from benchmark_context_iteration import sources
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.typechecking.typeinfer import check_type
    from aeon.verification import smt
    from aeon.verification.state import VerificationState

    results = []
    for case, source in sources().items():
        if args.case and case != args.case:
            continue
        driver = AeonDriver(AeonConfig("tdsyn_enumerative", SilentSynthesisUI(), 1, check_only=True, no_main=True))
        began = time.perf_counter()
        errors = list(driver.parse(filename=str(ROOT / "context-benchmark.ae"), aeon_code=source))
        parse_seconds = time.perf_counter() - began
        assert not errors, (case, [type(e).__name__ for e in errors])
        with driver.session.activate():
            smt.clear_smt_caches()
            gc.collect()
            uncertain = driver.session.state(VerificationState).inconclusive_queries
            began = time.perf_counter()
            valid = check_type(driver.typing_ctx, driver.core)
            elapsed = time.perf_counter() - began
            assert valid
            assert driver.session.state(VerificationState).inconclusive_queries == uncertain
        results.append(
            dict(
                case=case,
                seconds=elapsed,
                parse_seconds=parse_seconds,
                valid=valid,
                source_sha256=hashlib.sha256(source.encode()).hexdigest(),
            )
        )
    return results


def synthesize(args):
    from aeon.facade.driver import AeonConfig, AeonDriver
    from aeon.synthesis.uis.api import SilentSynthesisUI
    from aeon.synthesis.api import SynthesisNotSuccessful
    from aeon.synthesis import entrypoint, program_specifications
    from aeon.synthesis.modules.tdsyn.synthesizer import TDSynSynthesizer
    from aeon.core.terms import Application, Literal, Var
    from aeon.core.substitutions import substitution
    from aeon.core.types import t_unit
    from aeon.utils.name import Name

    paths = {
        "array_int_fit": "examples/synthesis/ortools/array_int.ae",
        "image_key": "examples/image/key.ae",
        "knapsack_50": "examples/synthesis/puzzle/knapsack_50.ae",
    }
    source = (
        (ROOT / paths[args.case]).read_text()
        if args.case in paths
        else ("import List; def result:{xs:(List {v:Int|v>=5 && v<=10})|List.size xs=20}:=?result;")
    )
    record = dict(
        case=args.case,
        budget_seconds=args.budget,
        seed=args.seed,
        attempts=0,
        validation_calls=0,
        validated=0,
        scored=0,
        finite_scored=0,
        typecheck_calls=0,
        typecheck_passed=0,
        typecheck_seconds=0.0,
        front=[],
        improvements=[],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
    )

    class UI(SilentSynthesisUI):
        def register(self, solution, quality, elapsed_time, is_best):
            if solution is not None and isinstance(quality, list):
                record.setdefault("first_solution_seconds", elapsed_time)
                if is_best and isinstance(quality, list):
                    record["improvements"].append(dict(seconds=elapsed_time, quality=quality))

        def register_front(self, front, elapsed_time):
            record["front"] = [list(quality) for quality, _ in front]

    driver = AeonDriver(AeonConfig("tdsyn_enumerative", UI(), args.budget, tdsyn_expansion="lazy"))
    began = time.perf_counter()
    errors = list(driver.parse(filename=str(ROOT / paths.get(args.case, "context-benchmark.ae")), aeon_code=source))
    record["parse_seconds"] = time.perf_counter() - began
    assert not errors, [type(e).__name__ for e in errors]
    assert driver.has_synth()
    target = driver.incomplete_functions[0][0]

    def timed(original):
        def check(*positional, **keyword):
            record["typecheck_calls"] += 1
            started = time.perf_counter()
            try:
                result = original(*positional, **keyword)
                record["typecheck_passed"] += bool(result)
                return result
            finally:
                record["typecheck_seconds"] += time.perf_counter() - started

        return check

    entrypoint.check_type = timed(entrypoint.check_type)
    program_specifications.check_type = timed(program_specifications.check_type)
    original = TDSynSynthesizer._try_complete

    def complete(self, partial, validate, evaluate, start_time, ui, front):
        if partial.is_complete():
            record["attempts"] += 1

        def checked(term):
            record["validation_calls"] += 1
            accepted = validate(term)
            record["validated"] += bool(accepted)
            return accepted

        def scored(term):
            result = evaluate(term)
            record["scored"] += 1
            record["finite_scored"] += bool(result and all(math.isfinite(float(x)) for x in result))
            return result

        return original(self, partial, checked, scored, start_time, ui, front)

    TDSynSynthesizer._try_complete = complete
    began = time.perf_counter()
    try:
        driver.synth()
        record["status"] = "solved"
    except SynthesisNotSuccessful:
        record["status"] = "no_solution"
    record["synthesis_seconds"] = time.perf_counter() - began
    if record["status"] == "solved":
        expression = Var(target)
        if args.case in ("array_int_fit", "knapsack_50"):
            expression = Application(expression, Literal(None, t_unit))
        driver.core = substitution(driver.core, expression, Name("main", 0))
        value = driver.run()
        if args.case == "image_key":
            assert value.size == (1024, 768)
            record["returned_size"] = list(value.size)
        elif args.case == "knapsack_50":
            assert isinstance(value, list) and len(value) == 50 and all(type(x) is bool for x in value)
            record["returned_value"] = value
        elif args.case == "array_int_fit":
            assert isinstance(value, list) and len(value) == 3
            record["returned_value"] = value
            record["returned_loss"] = sum((x - y) ** 2 for x, y in zip(value, [3, -7, 10]))
        else:
            items = []
            while isinstance(value, tuple) and len(value) == 3:
                _, head, value = value
                items.append(head)
            assert value == ("List_nil",) and len(items) == 20 and all(5 <= x <= 10 for x in items)
            record["returned_value"] = items
        record["runtime_checked"] = True
    return [record]


def containers(args):
    """Isolate branching/storage costs; these are not end-to-end solver times."""
    import tracemalloc
    from aeon.core.types import t_int
    from aeon.typechecking.context import TypingContext, VariableBinder
    from aeon.utils.name import Name

    rows = []
    for size in (64, 512, 2048):
        names = [Name("outer", i) for i in range(size)]
        children = [Name("child", i) for i in range(256)]
        typing = TypingContext([VariableBinder(n, t_int) for n in names]).with_var(Name("local"), t_int)

        def typing_forks():
            forks = [typing.with_var(name, t_int) for name in children]
            for child in forks:
                for name in (names[0], names[-1], Name("missing")):
                    assert child.type_of(name) is (None if name.name == "missing" else t_int)
            return forks

        gc.collect()
        began = time.perf_counter()
        forks = typing_forks()
        elapsed = time.perf_counter() - began
        del forks
        gc.collect()
        tracemalloc.start()
        forks = typing_forks()
        _current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        del forks
        rows.append(dict(case="typing_forks", size=size, branches=256, seconds=elapsed, peak_bytes=peak))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("verify", "synthesis", "containers"), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--baseline", default=BASELINE)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--budget", type=int, default=20)
    parser.add_argument("--case", choices=CASES)
    parser.add_argument("--variant", choices=VARIANTS)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--worker", action="store_true")
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.worker:
        sys.meta_path.insert(0, BaselineModules(args.variant, args.baseline))
        from loguru import logger

        logger.remove()
        random.seed(args.seed)
        import numpy as np

        np.random.seed(args.seed)
        rows = {"verify": verify, "synthesis": synthesize, "containers": containers}[args.mode](args)
        for row in rows:
            row.update(variant=args.variant, seed=args.seed)
        args.output.write_text(json.dumps(rows, indent=2) + "\n")
        return
    report = dict(
        baseline=args.baseline,
        mode=args.mode,
        budget=args.budget,
        repeats=args.repeats,
        python=sys.version,
        protocol="Sequential fresh processes, rotating variant order; baseline includes direct chunk reverse iteration. No solver validation is disabled.",
        results=[],
    )
    report["implementation_sha256"] = {
        path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        for path in (
            "aeon/typechecking/context.py",
            "aeon/utils/name.py",
            "aeon/utils/persistent.py",
            "aeon/verification/smt.py",
        )
    }
    for repeat in range(args.repeats):
        order = VARIANTS[repeat % len(VARIANTS) :] + VARIANTS[: repeat % len(VARIANTS)]
        for case in [args.case] if args.case else (CASES if args.mode == "synthesis" else [None]):
            for variant in [args.variant] if args.variant else order:
                path = args.output.parent / f"{args.mode}-{case or 'all'}-{repeat}-{variant}.json"
                command = [
                    sys.executable,
                    __file__,
                    "--worker",
                    "--mode",
                    args.mode,
                    "--variant",
                    variant,
                    "--seed",
                    str(repeat),
                    "--budget",
                    str(args.budget),
                    "--baseline",
                    args.baseline,
                    "--output",
                    str(path),
                ]
                if case:
                    command += ["--case", case]
                env = {
                    **os.environ,
                    "PYTHONHASHSEED": "0",
                    "PYTHONDONTWRITEBYTECODE": "1",
                    "PYTHONPATH": str(ROOT),
                    "OPENBLAS_NUM_THREADS": "1",
                    "OMP_NUM_THREADS": "1",
                    "MKL_NUM_THREADS": "1",
                }
                with path.with_suffix(".log").open("w") as log:
                    subprocess.run(
                        command,
                        cwd=ROOT,
                        env=env,
                        stdout=log,
                        stderr=subprocess.STDOUT,
                        check=True,
                        timeout=args.budget + 120 if args.mode == "synthesis" else 180,
                    )
                rows = json.loads(path.read_text())
                report["results"].extend(rows)
                args.output.write_text(json.dumps(report, indent=2) + "\n")
                print(json.dumps(rows), flush=True)


if __name__ == "__main__":
    main()
