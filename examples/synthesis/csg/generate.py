#!/usr/bin/env python3
"""Generate inverse-CSG benchmark instances for Aeon.

Implements the benchmark from Feser, Dillig & Solar-Lezama, "Metric Program
Synthesis for Inverse CSG" (arXiv:2206.06164).

Inverse CSG is programming-by-example over a bitmap: given a target image B
(a grid of pixels labelled inside/outside), synthesise a CSG program P in the
CAD DSL of the paper (Fig. 3) such that  forall (u,v). [[P]](u,v) == B(u,v).

Design notes
------------
The target image is a real 32x32 PNG (the paper uses 32x32 = 1024 examples),
rendered here with Pillow into `targets/`. The CAD DSL is an Aeon `inductive
Csg`; the paper's evaluation semantics (Fig. 4) and pixel-difference distance
metric (Sec. 3.2) run natively in `csg_metric.py` (PIL), because evaluating a
full bitmap as an in-language Aeon expression does not scale. The synthesis
problem is `@minimize_int(error shape)` over a hole of type `Csg`: Aeon's
distance-guided synthesis mirrors the paper's metric search, and `error` == 0
means the bitmap was reconstructed exactly.

Run this from the repository root:  python examples/synthesis/csg/generate.py
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import csg_metric  # noqa: E402

GRID = 32

# ---- CSG reference programs as Python tuples (mirroring the Aeon semantics) ----
# ('circle', cx, cy, r) | ('rect', x1,y1,x2,y2) | ('union', a, b) | ('diff', a, b)


def to_tuple(e):
    """Convert a generator tuple to the runtime tag form used by csg_metric."""
    t = e[0]
    if t == "circle":
        return ("Csg_Circle", e[1], e[2], e[3])
    if t == "rect":
        return ("Csg_Rect", e[1], e[2], e[3], e[4])
    if t == "union":
        return ("Csg_Union", to_tuple(e[1]), to_tuple(e[2]))
    if t == "diff":
        return ("Csg_Diff", to_tuple(e[1]), to_tuple(e[2]))
    raise ValueError(t)


def to_aeon(e):
    t = e[0]
    if t == "circle":
        return f"Circle {e[1]} {e[2]} {e[3]}"
    if t == "rect":
        return f"Rect {e[1]} {e[2]} {e[3]} {e[4]}"
    if t == "union":
        return f"Union ({to_aeon(e[1])}) ({to_aeon(e[2])})"
    if t == "diff":
        return f"Diff ({to_aeon(e[1])}) ({to_aeon(e[2])})"
    raise ValueError(t)


TEMPLATE = r"""# Inverse CSG benchmark: __TITLE__
#
# From Feser, Dillig & Solar-Lezama, "Metric Program Synthesis for Inverse CSG"
# (arXiv:2206.06164). Inverse CSG is programming-by-example over a bitmap: given
# a target image, recover a CSG program (Fig. 3 of the paper) that draws it.
#
#   E ::= Circle(x,y,r) | Rect(x1,y1,x2,y2) | E union E | E diff E      (Fig. 3)
#   inside Circle(x,y,r)      iff (x-u)^2 + (y-v)^2 < r^2                (Fig. 4)
#   inside Rect(x1,y1,x2,y2)  iff x1<=u<=x2 and y1<=v<=y2
#   inside (a union b)        iff inside a  or  inside b
#   inside (a diff b)         iff inside a  and not inside b
#
# Target image:  examples/synthesis/csg/targets/__NAME__.png   (__GRID__x__GRID__ bitmap)
#
# The per-pixel evaluation and the pixel-difference distance metric run natively
# (examples/synthesis/csg/csg_metric.py, via Pillow); a full bitmap is too large
# to evaluate as an in-language Aeon expression. `@minimize_int(error shape)`
# performs distance-guided synthesis as in the paper; error == 0 is an exact
# match. Run from the repository root so the relative paths below resolve.

open Csg

inductive Csg
| Circle (cx:Int) (cy:Int) (cr:Int) : Csg
| Rect (rx1:Int) (ry1:Int) (rx2:Int) (ry2:Int) : Csg
| Union (ua:Csg) (ub:Csg) : Csg
| Diff (da:Csg) (db:Csg) : Csg

# Pixel-difference distance between e's bitmap and the target (the paper's metric).
def error (e:Csg) : {n:Int | n >= 0} =
    native "(__import__('sys').path.insert(0, 'examples/synthesis/csg'), __import__('csg_metric').score(e, 'examples/synthesis/csg/targets/__NAME__.png'))[1]";

# Rasterise a CSG program to a PNG, so a synthesised shape can be viewed.
def render (e:Csg) (path:String) : Unit =
    native "(__import__('sys').path.insert(0, 'examples/synthesis/csg'), __import__('csg_metric').render(e, __GRID__, path))[1]";

# (a) Synthesis: recover a CSG program whose bitmap matches the target.
@minimize_int(error shape)
@hide(error, render, shape_solution)
def shape : Csg = ?hole;

# (b) The reference program that generated the target bitmap (error == 0):
#     __REF__
def shape_solution : Csg = __REF__;
"""


def gen(name, title, ref, n):
    rt = to_tuple(ref)
    target_path = os.path.join(HERE, "targets", f"{name}.png")
    csg_metric.render(rt, n, target_path)
    assert csg_metric.score(rt, target_path) == 0, "reference must reconstruct its own bitmap"
    out = (
        TEMPLATE.replace("__TITLE__", title)
        .replace("__NAME__", name)
        .replace("__GRID__", str(n))
        .replace("__REF__", to_aeon(ref))
    )
    path = os.path.join(HERE, f"{name}.ae")
    with open(path, "w") as f:
        f.write(out)
    print(f"wrote {path}  +  targets/{name}.png  ({n}x{n}, ref error = 0)")


BENCHMARKS = [
    ("csg_circle", "a single circle", ("circle", 16, 16, 10), GRID),
    ("csg_rectangle", "a rectangle", ("rect", 6, 6, 25, 18), GRID),
    (
        "csg_square_with_hole",
        "a square with a circular hole (Rect diff Circle)",
        ("diff", ("rect", 5, 5, 26, 26), ("circle", 16, 16, 8)),
        GRID,
    ),
    ("csg_two_circles", "the union of two circles", ("union", ("circle", 10, 16, 7), ("circle", 22, 16, 7)), GRID),
    (
        "csg_ring",
        "a ring / annulus (big Circle diff small Circle)",
        ("diff", ("circle", 16, 16, 12), ("circle", 16, 16, 6)),
        GRID,
    ),
]

if __name__ == "__main__":
    os.makedirs(os.path.join(HERE, "targets"), exist_ok=True)
    for args in BENCHMARKS:
        gen(*args)
