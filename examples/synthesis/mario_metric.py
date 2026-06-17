"""Native rasteriser for the Aeon Super Mario level generator (``supermario.ae``).

The SyMetric backend (``-s symetric``) clusters candidates by the *distance
between their outputs*, so it needs each candidate exposed as a numeric feature
vector rather than as an abstract ``Level`` value. Mirroring the inverse-CSG
benchmark's ``scene`` featuriser (``csg_metric.scene_vector``), this draws a
level into a 2D occupancy matrix and flattens it to a 1D 0/1 vector: two levels
are "close" when their drawn layouts overlap.

A ``Level`` arrives from Aeon as nested tagged tuples, e.g.

    ('Level_mk_level', <chunks>, <enemies>)
    <chunks>  = ('List_cons', <chunk>, ('List_cons', ..., ('List_nil',)))
    <chunk>   = ('Chunk_platform_chunk', x, y, w) | ('Chunk_gap_chunk', x, y, wg, wB, wA) | ...
    <enemy>   = ('Enemy_mk_enemy', ('MobType_goomba',), x)
    <box>     = ('Box_mk_box', ('BoxType_block_coin',), x, y)

The grid is ``HEIGHT`` rows x ``WIDTH`` columns. Columns are level x-positions
(chunk refinements keep x in [5, 95]); rows are height above the ground, which a
chunk's ``y`` (in [3, 5]) and any stack height address. Everything is clamped to
the grid, so out-of-range coordinates never raise -- they just clip.
"""

from __future__ import annotations

WIDTH = 100  # columns: level x-position (x lives in [5, 95], widths push a bit past)
HEIGHT = 8  # rows: height above the ground


def _list_to_py(v):
    """Flatten a cons/nil ``List`` value into a Python list of its elements."""
    out = []
    while isinstance(v, tuple) and v and v[0] == "List_cons":
        out.append(v[1])
        v = v[2]
    return out


def _fill(grid, r0, r1, c0, c1):
    """Mark every cell in rows [r0, r1] x columns [c0, c1) (inclusive rows),
    clamped to the grid so any coordinate is safe."""
    r0 = max(0, r0)
    r1 = min(HEIGHT - 1, r1)
    c0 = max(0, c0)
    c1 = min(WIDTH, c1)
    for r in range(r0, r1 + 1):
        row = grid[r]
        for c in range(c0, c1):
            row[c] = 1


def _draw_chunk(grid, chunk):
    """Paint one chunk's footprint into the grid."""
    if not (isinstance(chunk, tuple) and chunk):
        return
    tag = chunk[0]
    if tag == "Chunk_platform_chunk":  # (x, y, w): a one-thick platform at height y
        _, x, y, w = chunk
        _fill(grid, y, y, x, x + w)
    elif tag == "Chunk_hill_chunk":  # (x, y, w): a solid hill from the ground to y
        _, x, y, w = chunk
        _fill(grid, 0, y, x, x + w)
    elif tag == "Chunk_gap_chunk":  # (x, y, wg, wB, wA): ground with a gap in the middle
        _, x, y, wg, wb, wa = chunk
        _fill(grid, 0, 0, x, x + wb)
        _fill(grid, 0, 0, x + wb + wg, x + wb + wg + wa)
    elif tag == "Chunk_canon_chunk":  # (x, y, h, wB, wA): a 2-wide cannon of height h
        _, x, y, h, wb, wa = chunk
        _fill(grid, 0, h, x, x + 2)
    elif tag == "Chunk_tube_chunk":  # (x, y, h, wB, wA): a 2-wide pipe of height h
        _, x, y, h, wb, wa = chunk
        _fill(grid, 0, h, x, x + 2)
    elif tag == "Chunk_coin_chunk":  # (x, y, wc): a row of coins at height y
        _, x, y, wc = chunk
        _fill(grid, y, y, x, x + wc)
    elif tag == "Chunk_boxes_chunk":  # (bs): each box marked at its own (x, y)
        for box in _list_to_py(chunk[1]):
            if isinstance(box, tuple) and box and box[0] == "Box_mk_box":
                _, _bt, x, y = box
                _fill(grid, y, y, x, x + 1)


def _draw_enemy(grid, enemy):
    """Paint one enemy as a single mark just above the ground."""
    if isinstance(enemy, tuple) and enemy and enemy[0] == "Enemy_mk_enemy":
        _, _mob, x = enemy
        _fill(grid, 1, 1, x, x + 1)


def bitmap(level):
    """Render a ``Level`` to a HEIGHT x WIDTH grid of 0/1 cells."""
    grid = [[0] * WIDTH for _ in range(HEIGHT)]
    if isinstance(level, tuple) and level and level[0] == "Level_mk_level":
        for chunk in _list_to_py(level[1]):
            _draw_chunk(grid, chunk)
        for enemy in _list_to_py(level[2]):
            _draw_enemy(grid, enemy)
    return grid


def scene_vector(level):
    """The level's drawn layout as a flat 0/1 vector -- the feature SyMetric
    clusters individuals by (the 2D matrix flattened to 1D, top row first)."""
    return [cell for row in reversed(bitmap(level)) for cell in row]


def ascii_scene(level):
    """A human-readable rendering of the level grid (top row first), handy for
    eyeballing a synthesised level: '#' is filled, '.' is empty."""
    rows = ["".join("#" if cell else "." for cell in row) for row in reversed(bitmap(level))]
    return "\n".join(rows)
