#!/usr/bin/env python3
"""Generate the inverse-CSG benchmark suite for Aeon.

Reproduces the benchmark of Feser, Dillig & Solar-Lezama, "Metric Program
Synthesis for Inverse CSG" (arXiv:2206.06164). The exact target programs are the
authors' own benchmark scenes, taken verbatim from their SyMetric artifact
(github.com/jfeser/symetric, bench/cad_ext/) and listed in `benchmarks.tsv`
(category, name, program). Their CAD DSL maps directly onto an Aeon `inductive
Csg`:

    (circle x y r)      -> Circle x y r
    (rect x1 y1 x2 y2)  -> Rect x1 y1 x2 y2
    (union a b)         -> Union a b
    (sub a b)           -> Diff a b          (set difference)
    (repl e dx dy c)    -> Repeat e dx dy c   (c copies, copy i shifted by i*(dx,dy))

Each scene is rasterised exactly as scene2d.ml does -- an unscaled 16x16 grid
with scaling factor 2, i.e. a 32x32 bitmap -- by csg_metric.py, and saved as a
PNG under targets/. The per-pixel work is native because a full bitmap is far
too large to evaluate as an in-language Aeon expression.

Each emitted `<name>.ae` poses the inverse-CSG synthesis problem
`@minimize_int(error shape)` over a hole of type Csg (distance-guided synthesis,
as in the paper); the original program is kept as `shape_solution` and asserted
to reconstruct its own bitmap (error == 0).

Run from the repository root:  python examples/synthesis/csg/generate.py
"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import csg_metric  # noqa: E402

# ----------------------------- S-expression parser ----------------------------


def parse(text):
    """Parse one CAD S-expression into a nested tuple."""
    toks = text.replace("(", " ( ").replace(")", " ) ").split()
    pos = 0

    def read_int():
        # An integer argument, optionally wrapped in parens: `5` or `( 5 )`
        # (the generated benchmarks wrap every number in parentheses).
        nonlocal pos
        if toks[pos] == "(":
            pos += 1
            val = int(toks[pos])
            pos += 1
            assert toks[pos] == ")", f"expected ')' after int, got {toks[pos]!r}"
            pos += 1
            return val
        val = int(toks[pos])
        pos += 1
        return val

    def walk():
        nonlocal pos
        assert toks[pos] == "(", f"expected '(' got {toks[pos]!r}"
        pos += 1
        head = toks[pos]
        pos += 1
        if head == "circle":
            node = ("circle", read_int(), read_int(), read_int())
        elif head == "rect":
            node = ("rect", read_int(), read_int(), read_int(), read_int())
        elif head == "union":
            a, b = walk(), walk()
            node = ("union", a, b)
        elif head == "sub":
            a, b = walk(), walk()
            node = ("diff", a, b)
        elif head == "repl":
            sub = walk()
            node = ("repeat", sub, read_int(), read_int(), read_int())
        else:
            raise ValueError(f"unknown operator {head!r}")
        assert toks[pos] == ")", f"expected ')' got {toks[pos]!r}"
        pos += 1
        return node

    return walk()


def to_runtime(e):
    """Generator tuple -> the runtime tag form used by csg_metric."""
    t = e[0]
    if t == "circle":
        return ("Csg_Circle", e[1], e[2], e[3])
    if t == "rect":
        return ("Csg_Rect", e[1], e[2], e[3], e[4])
    if t == "union":
        return ("Csg_Union", to_runtime(e[1]), to_runtime(e[2]))
    if t == "diff":
        return ("Csg_Diff", to_runtime(e[1]), to_runtime(e[2]))
    if t == "repeat":
        return ("Csg_Repeat", to_runtime(e[1]), e[2], e[3], e[4])
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
    if t == "repeat":
        return f"Repeat ({to_aeon(e[1])}) {e[2]} {e[3]} {e[4]}"
    raise ValueError(t)


# --------------------------------- emission -----------------------------------

TEMPLATE = r"""# Inverse CSG benchmark "__CAT__/__BENCH__" (32x32).
#
# From Feser, Dillig & Solar-Lezama, "Metric Program Synthesis for Inverse CSG"
# (arXiv:2206.06164). The target scene is the authors' own benchmark, taken
# verbatim from their SyMetric artifact (github.com/jfeser/symetric,
# bench/cad_ext/__CAT__/__BENCH__):
#
#     __SEXPR__
#
# Inverse CSG is programming-by-example over a bitmap: recover a CSG program
# (Fig. 3 of the paper) that draws the target image. The CAD DSL:
#
#   E ::= Circle(x,y,r) | Rect(x1,y1,x2,y2)
#       | E union E | E diff E | Repeat(E,dx,dy,c)                      (Fig. 3)
#
# The scene (16x16, scaling 2 -> 32x32) is rasterised by csg_metric.py exactly
# as the tool's lib/scene2d.ml does; the per-pixel work runs natively (Pillow).
# Target image:  examples/synthesis/csg/targets/__NAME__.png
#
# The paper guides search by the Jaccard distance between bitmaps (Sec. 4.2),
# delta(A,B) = 1 - |A and B| / |A or B|, so `@minimize_float(jaccard shape)` does
# distance-guided synthesis exactly as in the paper. jaccard == 0 (equivalently
# the pixel difference `error` == 0) is an exact reconstruction. Run from the
# repository root.

open Csg

inductive Csg
| Circle (cx:Int) (cy:Int) (cr:Int) : Csg
| Rect (rx1:Int) (ry1:Int) (rx2:Int) (ry2:Int) : Csg
| Union (ua:Csg) (ub:Csg) : Csg
| Diff (da:Csg) (db:Csg) : Csg
| Repeat (re:Csg) (rx:Int) (ry:Int) (rc:Int) : Csg

# The paper's distance metric: Jaccard distance to the target (in [0,1], 0 = exact).
def jaccard (e:Csg) : Float =
    native "(__import__('sys').path.insert(0, 'examples/synthesis/csg'), __import__('csg_metric').jaccard_distance(e, 'examples/synthesis/csg/targets/__NAME__.png'))[1]";

# Pixel-difference (Hamming) distance: 0 exactly when the bitmap is reconstructed.
def error (e:Csg) : {n:Int | n >= 0} =
    native "(__import__('sys').path.insert(0, 'examples/synthesis/csg'), __import__('csg_metric').score(e, 'examples/synthesis/csg/targets/__NAME__.png'))[1]";

# Rasterise a CSG program to a PNG, so a synthesised shape can be viewed.
def render (e:Csg) (path:String) : Unit =
    native "(__import__('sys').path.insert(0, 'examples/synthesis/csg'), __import__('csg_metric').render(e, 32, path))[1]";

# (a) Synthesis: recover a CSG program, guided by the paper's Jaccard metric.
@minimize_float(jaccard shape)
@hide(jaccard, error, render, shape_solution)
def shape : Csg = ?hole;

# (b) The original benchmark program (reconstructs the target, error == 0):
def shape_solution : Csg = __REF__;
"""


def emit(cat, bench, sexpr):
    name = f"csg_{cat}_{bench}"
    ref = parse(sexpr)
    rt = to_runtime(ref)
    target = os.path.join(HERE, "targets", f"{name}.png")
    csg_metric.render(rt, csg_metric.SCALED, target)
    assert csg_metric.score(rt, target) == 0, f"{name}: reference must reconstruct its bitmap"
    out = (
        TEMPLATE.replace("__CAT__", cat)
        .replace("__BENCH__", bench)
        .replace("__NAME__", name)
        .replace("__SEXPR__", sexpr)
        .replace("__REF__", to_aeon(ref))
    )
    with open(os.path.join(HERE, f"{name}.ae"), "w") as f:
        f.write(out)
    return name


if __name__ == "__main__":
    os.makedirs(os.path.join(HERE, "targets"), exist_ok=True)
    n = 0
    with open(os.path.join(HERE, "benchmarks.tsv")) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            cat, bench, sexpr = line.split("\t")
            name = emit(cat, bench, sexpr.strip())
            n += 1
            print(f"wrote {name}.ae  +  targets/{name}.png")
    print(f"generated {n} benchmarks (ref error == 0 for all)")
