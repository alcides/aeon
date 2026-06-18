"""Tests for the AFTA backend's example-driven (PBE) mode.

These exercise the BLAZE/SYNGAR string-transformation construction (Wang, Dillig
& Singh, POPL'18) as ported onto aeon: a function hole carrying ``@example`` I/O
pairs is solved by building a tree automaton over the in-scope ``String`` DSL,
keyed on the per-example output vectors. Run through the real CLI driver so the
``@example`` decorator, the in-process probe, and the synthesizer are wired
exactly as in production.
"""

from __future__ import annotations

import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _run_pbe(src_text: str, tmp_path, budget: int = 40) -> str:
    src = tmp_path / "pbe.ae"
    src.write_text(src_text)
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", "--no-main", "-s", "afta", "--budget", str(budget), str(src)],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=180,
    )
    out = proc.stdout + proc.stderr
    assert "Traceback" not in proc.stderr, out[-2000:]
    assert "no program consistent" not in out, "AFTA(PBE) failed to find a solution:\n" + out[-2000:]
    return out


def test_pbe_extracts_prefix(tmp_path):
    """First three characters of a phone number -- the canonical SyGuS string
    benchmark. The expected solution is ``slice name 0 3``."""
    out = _run_pbe(
        "open String\n"
        '@example(f "938-242-504" = "938")\n'
        '@example(f "308-916-545" = "308")\n'
        '@example(f "623-599-749" = "623")\n'
        "def f (name: String) : String := (?hole : String);\n",
        tmp_path,
    )
    # A solved hole prints a concrete body for f built from the String DSL.
    assert "def f" in out, out[-2000:]
    assert "slice" in out, out[-2000:]


def test_pbe_identity(tmp_path):
    """When every output equals its input, the smallest consistent program is
    the parameter itself."""
    out = _run_pbe(
        "open String\n"
        '@example(g "hello" = "hello")\n'
        '@example(g "world" = "world")\n'
        "def g (s: String) : String := (?hole : String);\n",
        tmp_path,
        budget=20,
    )
    assert "def g" in out, out[-2000:]


def test_pbe_uppercase(tmp_path):
    """A single-component transformation: upper-case the input."""
    out = _run_pbe(
        "open String\n"
        '@example(h "abc" = "ABC")\n'
        '@example(h "aeon" = "AEON")\n'
        "def h (s: String) : String := (?hole : String);\n",
        tmp_path,
        budget=30,
    )
    assert "def h" in out, out[-2000:]
    assert "upper" in out, out[-2000:]


# --- Matrix / tensor domain (BLAZE Fig.17) --------------------------------


def test_pbe_matrix_reshape(tmp_path):
    """The paper's running matrix example: reshape a length-6 vector row-wise
    into a 2x3 matrix (matrices encoded MATLAB-style as strings)."""
    out = _run_pbe(
        "open Matrix\n"
        '@example(f "1,2,3,4,5,6" = "1,2,3;4,5,6")\n'
        '@example(f "7,8,9,10,11,12" = "7,8,9;10,11,12")\n'
        "def f (m: String) : String := (?hole : String);\n",
        tmp_path,
        budget=40,
    )
    assert "reshape" in out, out[-2000:]


def test_pbe_matrix_fliplr(tmp_path):
    """A single Fig.17 operator: flip a matrix left-right."""
    out = _run_pbe(
        "open Matrix\n"
        '@example(f "1,2,3;4,5,6" = "3,2,1;6,5,4")\n'
        '@example(f "7,8,9;10,11,12" = "9,8,7;12,11,10")\n'
        "def f (m: String) : String := (?hole : String);\n",
        tmp_path,
        budget=30,
    )
    assert "fliplr" in out, out[-2000:]
