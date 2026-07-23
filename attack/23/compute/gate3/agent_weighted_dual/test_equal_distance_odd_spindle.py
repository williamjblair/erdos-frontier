"""Exact hostile fixture for equal-distance two-demand strictness.

The eight-vertex odd-spindle instance is tight for ``3D <= 2(n-2)`` and
has no edge-disjoint routing of its two demands.  It therefore kills both a
stronger order claim and the tempting routing-based proof of the sharp one.
"""

from __future__ import annotations

from compute23.gate2.common import adj_masks, bfs_dist
from compute23.gate3.rl_lib import (
    all_dists,
    check_rfc_direct,
    slack_array,
    union_triangle_free,
    xor_bits,
)


N = 8
EDGES = (
    (0, 5),
    (1, 5),
    (0, 6),
    (2, 6),
    (3, 6),
    (1, 7),
    (2, 7),
    (4, 7),
)
DEMANDS = ((0, 4), (1, 3))


def _simple_paths(start: int, finish: int) -> list[tuple[int, ...]]:
    adjacency = adj_masks(N, list(EDGES))
    paths: list[tuple[int, ...]] = []

    def visit(path: tuple[int, ...]) -> None:
        u = path[-1]
        if u == finish:
            paths.append(path)
            return
        neighbors = adjacency[u]
        while neighbors:
            bit = neighbors & -neighbors
            neighbors -= bit
            v = bit.bit_length() - 1
            if v not in path:
                visit(path + (v,))

    visit((start,))
    return paths


def _edge_set(path: tuple[int, ...]) -> frozenset[tuple[int, int]]:
    return frozenset(tuple(sorted(edge)) for edge in zip(path, path[1:]))


def test_odd_spindle_exact_cut_and_order() -> None:
    adjacency = adj_masks(N, list(EDGES))
    assert all(distance >= 0 for distance in bfs_dist(N, adjacency, 0))
    distances = all_dists(N, list(EDGES))
    demand_distances = tuple(distances[u][v] for u, v in DEMANDS)
    assert demand_distances == (4, 4)
    assert union_triangle_free(N, list(EDGES), DEMANDS)

    slack = slack_array(N, list(EDGES), DEMANDS, xor_bits(N))
    assert int(slack.min()) == 0
    # Direct Python-integer reproduction, independent of the vectorized row.
    for root in range(N):
        # Adding no stub is exactly the symmetric pair cut condition; choosing
        # root=x0 makes the stub contribution identically zero.
        ok, witness = check_rfc_direct(
            N, list(EDGES), DEMANDS, root, root
        )
        assert ok, witness

    distance = demand_distances[0]
    assert 3 * distance == 2 * (N - 2)
    assert 3 * distance > 2 * (N - 3)


def test_odd_spindle_has_no_edge_disjoint_demand_routing() -> None:
    first = _simple_paths(*DEMANDS[0])
    second = _simple_paths(*DEMANDS[1])
    assert first and second
    assert not any(
        _edge_set(path0).isdisjoint(_edge_set(path1))
        for path0 in first
        for path1 in second
    )
