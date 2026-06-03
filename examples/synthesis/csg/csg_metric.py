"""Native (PIL) helpers for the Aeon inverse-CSG benchmark.

Implements the evaluation semantics (Fig. 4) and distance metric (Sec. 3.2) of
Feser, Dillig & Solar-Lezama, "Metric Program Synthesis for Inverse CSG"
(arXiv:2206.06164), reproducing the rasterisation used by the authors' SyMetric
tool (github.com/jfeser/symetric, lib/scene2d.ml). The per-pixel work runs
natively because a full bitmap is far too large to evaluate as an in-language
Aeon expression.

Scene: an unscaled DIM x DIM grid (the tool's default 16) rendered with a
scaling factor SCALING (default 2), i.e. a 32x32 bitmap, with primitive
coordinates given in the *unscaled* space (so `circle 8 8 7` is the same program
text as the benchmark file). Following scene2d.ml:

    circle(cx,cy,r) inside (x,y)        iff (x-S*cx)^2 + (y-S*cy)^2 < (S*r)^2
    rect(lx,ly,hx,hy) inside (x,y)      iff S*lx <= x <= S*hx and S*ly <= y <= S*hy
    union / sub                          or / and-not
    repl(e,dx,dy,c) inside (x,y)         iff e inside (x - S*i*dx, y - S*i*dy)
                                             for some 0 <= i < c

A CSG value arrives from Aeon as nested tuples, e.g.
    ('Csg_Diff', ('Csg_Rect', 5, 5, 26, 26), ('Csg_Circle', 16, 16, 8))
    ('Csg_Repeat', ('Csg_Circle', 5, 16, 2), 6, 0, 4)

The y axis is flipped on save (scene y grows upward, image rows grow downward),
matching the tool's display convention.
"""

from PIL import Image

DIM = 16
SCALING = 2
SCALED = DIM * SCALING  # 32


def contains(e, x, y):
    """Is scaled-space pixel (x, y) inside CSG shape e?  (Fig. 4 of the paper.)"""
    tag = e[0]
    if tag == "Csg_Circle":
        _, cx, cy, cr = e
        cx, cy, cr = cx * SCALING, cy * SCALING, cr * SCALING
        return (x - cx) ** 2 + (y - cy) ** 2 < cr * cr
    if tag == "Csg_Rect":
        _, x1, y1, x2, y2 = e
        return x1 * SCALING <= x <= x2 * SCALING and y1 * SCALING <= y <= y2 * SCALING
    if tag == "Csg_Union":
        return contains(e[1], x, y) or contains(e[2], x, y)
    if tag == "Csg_Diff":
        return contains(e[1], x, y) and not contains(e[2], x, y)
    if tag == "Csg_Repeat":
        # Union of c copies of the sub-shape, copy i translated by (i*dx, i*dy).
        _, sub, dx, dy, c = e
        sdx, sdy = dx * SCALING, dy * SCALING
        return any(contains(sub, x - i * sdx, y - i * sdy) for i in range(c))
    raise ValueError(f"unknown CSG node: {tag!r}")


def bitmap(e, scaled=SCALED):
    """Rasterise e to a list of rows (y flipped to match the tool's display)."""
    rows = []
    for r in range(scaled):
        y = scaled - 1 - r
        rows.append([1 if contains(e, x, y) else 0 for x in range(scaled)])
    return rows


def render(e, scaled, path):
    """Rasterise shape e and save it as a 1-bit PNG."""
    rows = bitmap(e, scaled)
    img = Image.new("1", (scaled, scaled), 0)
    px = img.load()
    for r in range(scaled):
        for x in range(scaled):
            px[x, r] = rows[r][x]
    img.save(path)
    return None


def score(e, target_path):
    """Pixel-difference distance between e's bitmap and the target PNG."""
    img = Image.open(target_path).convert("1")
    w, h = img.size
    tp = img.load()
    rows = bitmap(e, w)
    err = 0
    for r in range(h):
        for x in range(w):
            target = 1 if tp[x, r] else 0
            if target != rows[r][x]:
                err += 1
    return err
