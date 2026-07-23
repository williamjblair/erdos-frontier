"""Exact edge-disjoint-path completions for two prescribed even distances."""

from __future__ import annotations

from dataclasses import dataclass

from compute23.gate3.rl_lib import all_dists, slack_array, union_triangle_free, xor_bits


Edge = tuple[int, int]


@dataclass(frozen=True)
class TwoDistanceCompletion:
    order: int
    b_edges: tuple[Edge, ...]
    m_edges: tuple[Edge, Edge]
    requested_distances: tuple[int, int]
    completion_distances: tuple[int, int]
    minimum_cut_slack: int


def build_distinct_two_distance_completion(
    smaller: int, larger: int
) -> TwoDistanceCompletion:
    """Realize distinct even distances a<b in order b+1+a/2.

    One demand uses the main path P_b.  The other uses the edge-disjoint
    chain of two-edge detours over the first a path edges.
    """

    assert 4 <= smaller < larger and smaller % 2 == larger % 2 == 0
    b_edges: list[Edge] = [(i, i + 1) for i in range(larger)]
    next_vertex = larger + 1
    for block in range(smaller // 2):
        b_edges.append((2 * block, next_vertex))
        b_edges.append((next_vertex, 2 * block + 2))
        next_vertex += 1
    order = next_vertex
    m_edges = ((0, smaller), (0, larger))
    assert order == larger + 1 + smaller // 2
    assert union_triangle_free(order, b_edges, m_edges)
    distances = all_dists(order, b_edges)
    completion_distances = tuple(distances[u][v] for u, v in m_edges)
    assert completion_distances == (smaller, larger)
    slack = slack_array(order, b_edges, m_edges, xor_bits(order))
    assert int(slack.min()) >= 0
    return TwoDistanceCompletion(
        order,
        tuple(b_edges),
        m_edges,
        (smaller, larger),
        completion_distances,
        int(slack.min()),
    )


def build_equal_two_distance_completion(distance: int) -> TwoDistanceCompletion:
    """Realize two copies of even distance D in order 3D/2+2.

    The layered supply graph has alternating layer sizes 1,2,1,2,... and a
    final two-vertex layer.  The two star demands from the initial singleton
    have two edge-disjoint routes through every layer.
    """

    assert distance >= 4 and distance % 2 == 0
    layer_sizes = [1 if layer % 2 == 0 else 2 for layer in range(distance)] + [2]
    layers: list[list[int]] = []
    next_vertex = 0
    for size in layer_sizes:
        layer = list(range(next_vertex, next_vertex + size))
        layers.append(layer)
        next_vertex += size
    b_edges = [
        (u, v)
        for left, right in zip(layers, layers[1:])
        for u in left
        for v in right
    ]
    m_edges = ((layers[0][0], layers[-1][0]), (layers[0][0], layers[-1][1]))
    order = next_vertex
    assert order == 3 * distance // 2 + 2
    assert union_triangle_free(order, b_edges, m_edges)
    distances = all_dists(order, b_edges)
    completion_distances = tuple(distances[u][v] for u, v in m_edges)
    assert completion_distances == (distance, distance)
    slack = slack_array(order, b_edges, m_edges, xor_bits(order))
    assert int(slack.min()) >= 0
    return TwoDistanceCompletion(
        order,
        tuple(b_edges),
        m_edges,
        (distance, distance),
        completion_distances,
        int(slack.min()),
    )
