"""Native (PIL) helpers for the Aeon inverse-CSG benchmark.

Implements the evaluation semantics (Fig. 4) and pixel-difference metric (§3.2)
of Feser, Dillig & Solar-Lezama, "Metric Program Synthesis for Inverse CSG"
(arXiv:2206.06164), in Python so the per-pixel work runs natively rather than as
a (very slow) in-language Aeon expression.

A CSG value arrives from Aeon as nested tuples, e.g.
    ('Csg_Diff', ('Csg_Rect', 5, 5, 26, 26), ('Csg_Circle', 16, 16, 8))

`score(e, target_path)` returns the number of pixels where shape `e` disagrees
with the target bitmap (the metric the synthesiser minimises). `render(e, n,
path)` rasterises a shape to a PNG so results can be inspected as images.
"""

from PIL import Image


def contains(e, u, v):
    """Is pixel (u, v) inside CSG shape e?  (Fig. 4 of the paper.)"""
    tag = e[0]
    if tag == "Csg_Circle":
        _, cx, cy, cr = e
        return (cx - u) ** 2 + (cy - v) ** 2 < cr * cr
    if tag == "Csg_Rect":
        _, x1, y1, x2, y2 = e
        return x1 <= u <= x2 and y1 <= v <= y2
    if tag == "Csg_Union":
        return contains(e[1], u, v) or contains(e[2], u, v)
    if tag == "Csg_Diff":
        return contains(e[1], u, v) and not contains(e[2], u, v)
    raise ValueError(f"unknown CSG node: {tag!r}")


def render(e, n, path):
    """Rasterise shape e on an n x n grid and save it as a 1-bit PNG."""
    img = Image.new("1", (n, n), 0)
    px = img.load()
    for v in range(n):
        for u in range(n):
            if contains(e, u, v):
                px[u, v] = 1
    img.save(path)
    return None


def score(e, target_path):
    """Pixel-difference distance between e's bitmap and the target PNG."""
    img = Image.open(target_path).convert("1")
    w, h = img.size
    px = img.load()
    err = 0
    for v in range(h):
        for u in range(w):
            target = 1 if px[u, v] else 0
            got = 1 if contains(e, u, v) else 0
            if target != got:
                err += 1
    return err
