"""Host validation for the parallel Aeon Floyd–Warshall example."""

from __future__ import annotations

import math

from aeon.bindings.ndarray import NDArray


def prepare_graph(graph: NDArray) -> NDArray:
    """Validate a weighted adjacency matrix and include empty self paths."""
    if graph.rank != 2 or graph.shape[0] != graph.shape[1]:
        raise ValueError("Floyd–Warshall requires a square adjacency matrix")
    if any(math.isnan(weight) or weight == -math.inf for weight in graph.data):
        raise ValueError("Edge weights must be finite or positive infinity")
    n = graph.shape[0]
    for i in range(n):
        index = i * n + i
        graph.data[index] = min(graph.data[index], 0.0)
    return graph


def check_negative_cycles(distances: NDArray) -> NDArray:
    """Return the distance matrix, or reject graphs without finite shortest paths."""
    if distances.rank != 2 or distances.shape[0] != distances.shape[1]:
        raise ValueError("Floyd–Warshall requires a square distance matrix")
    n = distances.shape[0]
    if any(distances.data[i * n + i] < 0.0 for i in range(n)):
        raise ValueError("Graph contains a negative-weight cycle")
    return distances
