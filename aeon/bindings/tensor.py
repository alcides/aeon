"""Python bindings for the Aeon ``Tensor`` library.

Only the operations that need to bridge Aeon's runtime data structures to
numpy live here; the bulk of ``Tensor`` is expressed directly as native
numpy expressions in ``libraries/Tensor.ae``.

An Aeon inductive ``List`` is represented at runtime as nested tuples
``('List_cons', head, tail)`` terminated by ``('List_nil',)``. ``Vector``
and ``Matrix`` are numpy arrays.
"""

from __future__ import annotations

import numpy as np


def Tensor_from_list(xs):
    """Convert an Aeon ``List Float`` into a 1-D numpy float array."""
    out = []
    node = xs
    while isinstance(node, tuple) and node and node[0] == "List_cons":
        out.append(float(node[1]))
        node = node[2]
    return np.array(out, dtype=float)
