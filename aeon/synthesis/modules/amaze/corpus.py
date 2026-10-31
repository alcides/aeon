"""Audited package-only collection. Never evaluate a module's top-level spine."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import random
from pathlib import Path
from time import monotonic

from aeon.backend.evaluator import EvaluationContext, eval as aeon_eval
from aeon.compilation.compile import compile_program
from aeon.compilation.resolve import get_package_libraries_dir, resolve_import_path
from aeon.compilation.session import CompilationOptions, CompilationSession
from aeon.core.multiplicity import MOmega
from aeon.core.terms import Rec
from aeon.prelude.prelude import evaluation_vars
from aeon.sugar.parser import parse_main_program
from aeon.sugar.program import SAnnotation, SApplication, SIf, SLet, SLiteral, STypeApplication, SVar
from aeon.sugar.stypes import STypeConstructor
from aeon.typechecking.typeinfer import check_type
from .core import unwrap
from .grammar import Expr, SIGNATURES, evaluate, probes


class CorpusError(ValueError):
    pass


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def root() -> Path:
    path = get_package_libraries_dir()
    if path is None:
        raise CorpusError("packaged aeon/libraries is missing; install Aeon with its standard library")
    return path.resolve(strict=True)


def checked_path(path: Path, base: Path) -> Path:
    resolved = path.resolve(strict=True)
    if not resolved.is_relative_to(base):
        raise CorpusError(f"stdlib symlink escapes canonical package root: {path}")
    return resolved


def source_inventory() -> dict:
    base = root()
    files = {}
    for path in sorted(base.rglob("*.ae")):
        canonical = checked_path(path, base)
        files[path.relative_to(base).as_posix()] = {
            "canonical_path": str(canonical),
            "sha256": digest(canonical.read_bytes()),
        }
    return {"root": str(base), "files": files}


@dataclass
class Task:
    id: str
    module: str
    source: str
    source_hash: str
    inputs: tuple[str, ...]
    reference: Expr
    variables: tuple
    type: object
    ctx: object
    session: CompilationSession
    examples: tuple
    group: str
    split: str = ""

    def record(self):
        return {
            "id": self.id,
            "module": self.module,
            "source": self.source,
            "source_sha256": self.source_hash,
            "input_sorts": self.inputs,
            "result_sort": self.reference.sort,
            "reference": self.reference.data(),
            "examples": self.examples,
            "group": self.group,
            "split": self.split,
        }


def _scalar(ty):
    return isinstance(ty, STypeConstructor) and ty.name.name in ("Int", "Bool") and not ty.args


def _pure(term, variables):
    if isinstance(term, SLiteral):
        return _scalar(term.type) and (type(term.value) is bool or term.value in (0, 1))
    if isinstance(term, SVar):
        return term.name.name in variables or term.name.name in set(SIGNATURES) | {"==", "!="}
    if isinstance(term, SApplication):
        return _pure(term.fun, variables) and _pure(term.arg, variables)
    if isinstance(term, STypeApplication):
        return _scalar(term.type) and _pure(term.body, variables)
    if isinstance(term, SAnnotation):
        return _scalar(term.type) and _pure(term.expr, variables)
    if isinstance(term, SIf):
        return all(_pure(x, variables) for x in (term.cond, term.then, term.otherwise))
    if isinstance(term, SLet) and term.multiplicity is MOmega:
        return _pure(term.var_value, variables) and _pure(term.body, variables | {term.var_name.name})
    return False


def _reason(d):
    if d.foralls or d.rforalls or d.decorators or d.is_theorem:
        return "polymorphic/refinement-polymorphic/decorated/theorem definition"
    if not d.args or len(d.args) > 3 or not _scalar(d.type) or not all(_scalar(t) for _, t in d.args):
        return "outside first-order scalar functions with one to three inputs"
    if any(d.multiplicity_of(i) is not MOmega or d.is_instance_arg(i) for i in range(len(d.args))):
        return "unsupported multiplicity or instance parameter"
    if not _pure(d.body, {n.name for n, _ in d.args}):
        return "native/effectful, recursive, dependent, non-base-literal or unsupported body"
    return None


def _definition_source(text, definition):
    # Read the original source span, never parse pretty-printed Core text.
    lines = text.splitlines(keepends=True)
    start_line, start_column = definition.loc.start
    end_line, end_column = definition.loc.end
    start = sum(map(len, lines[: start_line - 1])) + start_column - 1
    end = sum(map(len, lines[: end_line - 1])) + end_column - 1
    return text[start:end].rstrip().rstrip(";") + ";\n"


def collect(seed: int = 0, deadline=float("inf")) -> tuple[list[Task], dict]:
    inventory = source_inventory()
    base = root()
    programs, parse_errors = {}, {}
    for relative in inventory["files"]:
        if monotonic() >= deadline:
            raise CorpusError("corpus collection budget exhausted")
        try:
            programs[relative] = parse_main_program((base / relative).read_text(), filename=str(base / relative))
        except Exception as exc:
            parse_errors[relative] = f"{type(exc).__name__}: {exc}"
    report = {**inventory, "parse_errors": parse_errors, "definitions": [], "dependencies": {}}
    session_options = CompilationOptions(package_only_imports=True)

    # Audit transitive resolution even though the supported extracted bodies are
    # closed over primitives/parameters and never call these dependencies.
    def dependencies(relative, visiting):
        if relative in visiting:
            raise CorpusError("cyclic stdlib imports")
        if relative not in programs:
            raise CorpusError(f"unparseable stdlib dependency: {relative}")
        result = {}
        for imp in programs[relative].imports:
            path = resolve_import_path(imp)
            if path is None:
                raise CorpusError(f"missing packaged stdlib dependency: {imp.module_path}")
            canonical = checked_path(Path(path), base)
            name = canonical.relative_to(base).as_posix()
            result[name] = inventory["files"][name]["sha256"]
            result.update(dependencies(name, visiting | {relative}))
        return result

    tasks = []
    for relative, program in programs.items():
        with CompilationSession(session_options).activate():
            try:
                report["dependencies"][relative] = dependencies(relative, set())
                dep_error = None
            except CorpusError as exc:
                dep_error = str(exc)
        for definition in program.definitions:
            task_id = f"{relative}:{definition.name.name}"
            record = {"id": task_id, "source": relative, "function": definition.name.name}
            report["definitions"].append(record)
            reason = dep_error or _reason(definition)
            if reason:
                record.update(status="skipped", reason=reason)
                continue
            session = CompilationSession(session_options)
            try:
                with session.activate():
                    # Compile only the audited pure source span. This prevents
                    # refinement execution from initializing unrelated FFI code.
                    unit, errors = compile_program(
                        _definition_source((base / relative).read_text(), definition),
                        filename=str(base / relative),
                        is_main=True,
                        is_main_hole=False,
                        use_cache=False,
                        write_cache=False,
                    )
                    if errors or not isinstance(unit.core_spine, Rec):
                        raise ValueError("isolated compiler rejected reference: " + str(errors))
                    d = unit.core_spine
                    variables, inputs, expression = unwrap(d.var_value, d.var_type)
                    if not check_type(unit.typing_ctx, d.var_value, d.var_type):
                        raise ValueError("reference failed ordinary typechecking")
                    function = aeon_eval(d.var_value, EvaluationContext(evaluation_vars))
                    examples = []
                    for arguments in probes(inputs):
                        output = function
                        for arg in arguments:
                            output = output(arg)
                        if output != evaluate(expression, arguments) or type(output) is not (
                            int if expression.sort == "Int" else bool
                        ):
                            raise ValueError("Core/reference interpreter disagreement")
                        examples.append((arguments, output))
                    group = digest(json.dumps([inputs, expression.data()], sort_keys=True).encode())
                    tasks.append(
                        Task(
                            task_id,
                            Path(relative).stem,
                            relative,
                            inventory["files"][relative]["sha256"],
                            inputs,
                            expression,
                            variables,
                            d.var_type,
                            unit.typing_ctx,
                            session,
                            tuple(examples),
                            group,
                        )
                    )
                    record.update(status="eligible", group=group)
            except Exception as exc:
                record.update(status="skipped", reason=f"{type(exc).__name__}: {exc}")
    groups = sorted({t.group for t in tasks})
    random.Random(seed).shuffle(groups)
    if len(groups) < 6:
        report["eligible"] = len(tasks)
        raise CorpusError(
            f"need at least six independent eligible stdlib function groups; found {len(groups)}. Corpus report: {json.dumps(report)}"
        )
    train_end = max(3, len(groups) * 3 // 5)
    validation_end = train_end + max(1, (len(groups) - train_end) // 2)
    splits = {
        g: "train" if i < train_end else "validation" if i < validation_end else "held_out"
        for i, g in enumerate(groups)
    }
    for task in tasks:
        task.split = splits[task.group]
    report.update(
        eligible=len(tasks),
        skipped=sum(r["status"] == "skipped" for r in report["definitions"]),
        tasks=[t.record() for t in tasks],
        split_counts={s: sum(t.split == s for t in tasks) for s in ("train", "validation", "held_out")},
        split_policy="seeded alpha-equivalent reference/signature groups, before mining; 60/20/20 with nonempty splits",
    )
    return tasks, report
