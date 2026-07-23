"""Exact private-path completion for a finite demand metric."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from compute23.gate2.common import adj_masks
from compute23.gate3.rl_lib import all_dists, slack_array, union_triangle_free, xor_bits


Edge = tuple[int, int]


def _components_on_edges(vertices: set[int], edges: tuple[Edge, ...]) -> list[set[int]]:
    adjacency = {vertex: set() for vertex in vertices}
    for u, v in edges:
        adjacency[u].add(v)
        adjacency[v].add(u)
    unseen = set(vertices)
    components = []
    while unseen:
        start = min(unseen)
        component = {start}
        stack = [start]
        unseen.remove(start)
        while stack:
            u = stack.pop()
            for v in adjacency[u]:
                if v in unseen:
                    unseen.remove(v)
                    component.add(v)
                    stack.append(v)
        components.append(component)
    return components


def _bipartite_sides(n: int, edges: list[Edge]) -> list[int]:
    adjacency = adj_masks(n, edges)
    sides = [-1] * n
    for start in range(n):
        if sides[start] >= 0:
            continue
        sides[start] = 0
        stack = [start]
        while stack:
            u = stack.pop()
            neighbors = adjacency[u]
            while neighbors:
                v = (neighbors & -neighbors).bit_length() - 1
                neighbors &= neighbors - 1
                if sides[v] < 0:
                    sides[v] = 1 - sides[u]
                    stack.append(v)
                else:
                    assert sides[v] != sides[u]
    return sides


@dataclass(frozen=True)
class PrivatePathCompletion:
    order: int
    endpoint_count: int
    distance_sum: int
    b_edges: tuple[Edge, ...]
    m_edges: tuple[Edge, ...]
    bridge_edges: tuple[Edge, ...]
    input_distances: tuple[int, ...]
    completion_distances: tuple[int, ...]
    minimum_cut_slack: int


def build_private_path_completion(
    *,
    ambient_n: int,
    ambient_b_edges: tuple[Edge, ...] | list[Edge],
    m_edges: tuple[Edge, ...] | list[Edge],
    check_all_cuts: bool = True,
) -> PrivatePathCompletion:
    """Build one edge-disjoint private B-path of ambient length per M-edge.

    Components of the M-graph are connected by B-bridges in a chain.  The
    endpoint labels are compacted first; every private internal vertex is
    fresh.  This realizes the exact order

        |V(M)| + sum_e (D_e - 1).
    """

    ambient_b_edges = tuple(tuple(sorted(edge)) for edge in ambient_b_edges)
    m_edges = tuple(tuple(sorted(edge)) for edge in m_edges)
    assert m_edges and len(set(m_edges)) == len(m_edges)
    endpoints = sorted({vertex for edge in m_edges for vertex in edge})
    endpoint_index = {vertex: index for index, vertex in enumerate(endpoints)}
    compact_m = tuple(
        tuple(sorted((endpoint_index[u], endpoint_index[v]))) for u, v in m_edges
    )
    ambient_distances = all_dists(ambient_n, list(ambient_b_edges))
    input_distances = tuple(ambient_distances[u][v] for u, v in m_edges)
    assert all(distance >= 4 and distance % 2 == 0 for distance in input_distances)

    next_vertex = len(endpoints)
    completion_b: list[Edge] = []
    for (u, v), distance in zip(compact_m, input_distances):
        previous = u
        for _ in range(distance - 1):
            completion_b.append(tuple(sorted((previous, next_vertex))))
            previous = next_vertex
            next_vertex += 1
        completion_b.append(tuple(sorted((previous, v))))
    order = next_vertex
    assert order == len(endpoints) + sum(distance - 1 for distance in input_distances)
    assert len(set(completion_b)) == len(completion_b)

    # Each M-component is already connected by its private paths.  Connect
    # those blocks in a chain.  The chain edges are bridges, so they cannot
    # create a route which leaves and re-enters one M-component.
    demand_components = _components_on_edges(set(range(len(endpoints))), compact_m)
    bridge_edges: list[Edge] = []
    for left, right in zip(demand_components, demand_components[1:]):
        bridge = tuple(sorted((min(left), min(right))))
        assert bridge not in compact_m and bridge not in completion_b
        completion_b.append(bridge)
        bridge_edges.append(bridge)

    # The initially disjoint path blocks are bipartite because every path
    # has even length.  A tree of component bridges can always be colored by
    # independently flipping a whole block; the generic checker confirms the
    # resulting unlabeled graph is bipartite (the chain choice already has a
    # compatible coloring in every audited instance).
    _bipartite_sides(order, completion_b)
    assert union_triangle_free(order, completion_b, compact_m)

    completion_distances_matrix = all_dists(order, completion_b)
    completion_distances = tuple(
        completion_distances_matrix[u][v] for u, v in compact_m
    )
    assert completion_distances == input_distances

    minimum_cut_slack = 0
    if check_all_cuts:
        bit = xor_bits(order)
        slack = slack_array(order, completion_b, compact_m, bit)
        minimum_cut_slack = int(slack.min())
        assert minimum_cut_slack >= 0
    return PrivatePathCompletion(
        order=order,
        endpoint_count=len(endpoints),
        distance_sum=sum(input_distances),
        b_edges=tuple(completion_b),
        m_edges=compact_m,
        bridge_edges=tuple(bridge_edges),
        input_distances=input_distances,
        completion_distances=completion_distances,
        minimum_cut_slack=minimum_cut_slack,
    )
