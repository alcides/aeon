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

# A synthesised `Repeat e dx dy c` can carry an arbitrarily large count `c`.
# Evaluating it literally is `c` recursive `contains` calls per pixel, so an
# unconstrained candidate (e.g. c in the millions) would make a single fitness
# evaluation effectively hang. The whole grid is only SCALED wide, so any copy
# beyond SCALED is fully off-screen and cannot change the bitmap; clamp the
# count so evaluation stays bounded.
MAX_REPEAT = SCALED


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
        n = min(max(c, 0), MAX_REPEAT)
        return any(contains(sub, x - i * sdx, y - i * sdy) for i in range(n))
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
    """Pixel-difference (Hamming) distance between e's bitmap and the target.

    This is 0 exactly when e reconstructs the target, and is used for the
    exact-match checks. The synthesiser is guided by `jaccard_distance` below.
    """
    img = Image.open(target_path).convert("1")
    w, h = img.size
    tp = img.load()
    try:
        rows = bitmap(e, w)
    except Exception:
        # A malformed or pathologically deep candidate evaluates to the
        # worst-possible distance rather than crashing the synthesiser.
        return w * h
    err = 0
    for r in range(h):
        for x in range(w):
            target = 1 if tp[x, r] else 0
            if target != rows[r][x]:
                err += 1
    return err


def jaccard_distance(e, target_path):
    """The paper's distance metric (Sec. 4.2): Jaccard distance between bitmaps.

    delta(A, B) = 1 - |A intersect B| / |A union B|, with delta = 0 for two
    empty scenes. This mirrors the tool's Scene2d.jaccard_pixels. It lies in
    [0, 1] and is 0 exactly when e reconstructs the target, so it is what the
    metric synthesiser minimises.
    """
    img = Image.open(target_path).convert("1")
    w, h = img.size
    tp = img.load()
    try:
        rows = bitmap(e, w)
    except Exception:
        # Worst-possible distance for a candidate that cannot be rasterised,
        # so the synthesiser is steered away from it instead of crashing.
        return 1.0
    inter = 0
    union = 0
    for r in range(h):
        for x in range(w):
            a = rows[r][x]
            b = 1 if tp[x, r] else 0
            if a and b:
                inter += 1
            if a or b:
                union += 1
    if union == 0:
        return 0.0
    return 1.0 - inter / union
