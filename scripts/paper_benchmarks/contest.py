"""Import all ASAC problems as pure text transformations with existing I/O data."""

import gzip
import hashlib
import json

from .common import digest, identifier


def asac(corpus):
    for directory in sorted((corpus.source_root / "asac").iterdir()):
        statement = directory / "task_e.md"
        if not statement.exists():
            continue
        inputs = sorted((directory / "tests/origin_form").glob("*.in"))
        assert inputs, directory
        cases = []
        origins = []
        for path in inputs:
            answer = directory / "tests/ans" / (path.stem + ".out")
            assert answer.exists(), answer
            # Remove an optional BOM and normalize CRLF through read_text.
            cases.append([path.read_text(encoding="utf-8-sig"), answer.read_text(encoding="utf-8-sig")])
            origins.append({"input": path.name, "input_sha256": digest(path), "output_sha256": digest(answer)})
        slug = identifier(directory.name)
        payload = (json.dumps(cases, ensure_ascii=True, separators=(",", ":")) + "\n").encode()
        checksum = hashlib.sha256(payload).hexdigest()
        data_dir = corpus.output / "asac/data"
        data_dir.mkdir(parents=True, exist_ok=True)
        data_path = data_dir / (slug + ".json.gz")
        if not data_path.exists() or gzip.decompress(data_path.read_bytes()) != payload:
            data_path.write_bytes(gzip.compress(payload, compresslevel=6, mtime=0))
        # Include one complete case so the file remains an inspectable example
        # even before downloading the larger evaluation corpus.
        small = min(cases, key=lambda row: sum(map(len, row)))
        source, expected = map(json.dumps, small)
        score = (
            f"__import__('aeon.benchmarks.paper_io', fromlist=['failures']).failures('{slug}', '{checksum}', candidate)"
        )
        code = "open Seq\nopen Contest\n\n"
        code += f"def corpusFailures (candidate:(input:String) -> String) : Int := native {json.dumps(score)};\n\n"
        code += f"@example(Contest.sameTokens (target {source}) {expected})\n"
        code += "@minimize_int(corpusFailures target)\ndef target (input:String) : String := ?hole;\n"
        corpus.add(
            "asac",
            slug,
            statement,
            code,
            specification="token-exact-io",
            examples=len(cases),
            data_sha256=checksum,
            original_tests=origins,
            original_specification="MiniZinc constraints; the Aeon port uses the provided I/O pairs",
            limitation="Exact output tokens; alternate valid witnesses and floating-point tolerances are not inferred.",
        )
