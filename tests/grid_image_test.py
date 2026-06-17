"""Tests for the 2D-grid helpers used by the Super Mario example: the Array
library additions (``build_grid``, ``count_ge``, ``zip_plus``), the Image
``from_grid`` black & white renderer, and the grid-based ``coverage`` /
``conflicts`` / PNG export defined in ``examples/synthesis/supermario.ae``.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SUPERMARIO = os.path.join(REPO, "examples", "synthesis", "supermario.ae")


def _run(src: str, tmp_path) -> str:
    f = tmp_path / "prog.ae"
    f.write_text(src)
    proc = subprocess.run(
        [sys.executable, "-m", "aeon", str(f)],
        cwd=REPO,
        capture_output=True,
        text=True,
        timeout=120,
    )
    out = proc.stdout + proc.stderr
    assert "Type error" not in out, out[-2000:]
    assert "Traceback" not in proc.stderr, out[-2000:]
    return out


def _numbers(out: str) -> list[int]:
    return [int(m) for m in re.findall(r"^(\d+)$", out, re.MULTILINE)]


def test_array_grid_helpers_and_from_grid(tmp_path):
    # build_grid materialises an h x w matrix; zip_plus overlays two rows;
    # count_ge counts cells over a threshold; from_grid renders a B&W PNG.
    png = tmp_path / "g.png"
    src = (
        "open Array\n"
        "open Image\n"
        "def diag (r: Int) (col: Int) : Int := if r = col then 1 else 0;\n"
        "def count_cells_ge (g: (Array (Array Int))) (t: Int) (i: {n:Int | n >= 0}) : Int :=\n"
        "    if i < Array.length g then Array.count_ge (Array.get g i) t + count_cells_ge g t (i + 1) else 0;\n"
        "def overlay_from (a: (Array (Array Int))) (b: (Array (Array Int))) (i: {n:Int | n >= 0}) : (Array (Array Int)) :=\n"
        "    if i < Array.length a && i < Array.length b\n"
        "    then Array.cons (overlay_from a b (i + 1)) (Array.zip_plus (Array.get a i) (Array.get b i)) else Array.new;\n"
        "def main (args: Int) : Unit :=\n"
        "    g := Array.build_grid 5 5 diag;\n"
        "    o := overlay_from g g 0;\n"
        f'    _ := Image.save (Image.from_grid g) "{png}";\n'
        "    _ := print (count_cells_ge g 1 0);\n"
        "    print (count_cells_ge o 2 0);\n"
    )
    out = _run(src, tmp_path)
    # 5x5 diagonal: 5 cells set; overlaid with itself every set cell is 2.
    assert _numbers(out)[:2] == [5, 5], out[-1500:]
    assert png.exists()
    from PIL import Image as PILImage

    im = PILImage.open(png)
    assert im.size == (5, 5)
    assert sum(1 for p in im.getdata() if p == (0, 0, 0)) == 5


def test_supermario_grid_coverage_conflicts_and_png(tmp_path):
    # Reuse the example's grid machinery on a concrete level: two platforms that
    # share columns 12..17 (conflicts) plus an enemy (coverage only).
    head = []
    for line in open(SUPERMARIO):
        if line.startswith("@cluster"):
            break
        head.append(line)
    png = tmp_path / "level.png"
    demo = (
        "\ndef demo : Level :=\n"
        "    Level_mk_level\n"
        "      (List_cons (Chunk_platform_chunk 9 5 9) (List_cons (Chunk_platform_chunk 12 5 6) List_nil))\n"
        "      (List_cons (Enemy_mk_enemy MobType_goomba 20) List_nil);\n"
        "def main (args: Int) : Unit :=\n"
        f'    _ := export_png demo "{png}";\n'
        "    _ := print (coverage demo);\n"
        "    print (conflicts demo);\n"
    )
    out = _run("".join(head) + demo, tmp_path)
    nums = _numbers(out)
    # coverage: union of the two platform rows (cols 9..17 = 9) + 1 enemy = 10.
    # conflicts: the platforms overlap on cols 12..17 = 6 cells.
    assert nums[:2] == [10, 6], out[-1500:]
    assert png.exists()
    from PIL import Image as PILImage

    im = PILImage.open(png)
    assert im.size == (100, 15)  # the paper's grid: 100 wide, Mario AI height 15
