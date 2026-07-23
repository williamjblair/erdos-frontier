"""Exact distance-preserving boundary completion for an off-corridor component."""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np

from compute23.gate2.common import adj_masks
from compute23.gate3.rl_lib import (
    all_dists,
    check_rfc_direct,
    slack_array,
    union_triangle_free,
    xor_bits,
)

from compute23.gate3.agent_aggregation.quotient_cut_average import off_components


Edge = tuple[int, int]


def _is_bipartite_connected(n: int, edges: list[Edge]) -> bool:
    adjacency = adj_masks(n, edges)
    side = [-1] * n
    side[0] = 0
    stack = [0]
    while stack:
        u = stack.pop()
        neighbors = adjacency[u]
        while neighbors:
            v = (neighbors & -neighbors).bit_length() - 1
            neighbors &= neighbors - 1
            if side[v] < 0:
                side[v] = 1 - side[u]
                stack.append(v)
            elif side[v] == side[u]:
                return False
    return all(value >= 0 for value in side)


@dataclass(frozen=True)
class BoundaryCompletion:
    component: tuple[int, ...]
    attachments: tuple[tuple[int, int], ...]
    spoke_lengths: tuple[int, ...]
    order: int
    b_edges: tuple[Edge, ...]
    m_edges: tuple[Edge, ...]
    root: int
    ambient_m_distances: tuple[int, ...]
    component_m_distances: tuple[int, ...]
    completion_m_distances: tuple[int, ...]
    minimum_cut_slack: int


def build_boundary_completion(
    *,
    n: int,
    b_edges: tuple[Edge, ...] | list[Edge],
    m_edges: tuple[Edge, ...] | list[Edge],
    path: tuple[int, ...],
    component: tuple[int, ...],
    check_all_completion_cuts: bool = True,
) -> BoundaryCompletion:
    """Construct the smaller valid completion described in the proof note.

    The component must contain at least one internal M-edge.  One private
    spoke is used for every attachment edge, so multiplicity two at one
    component vertex is represented in a simple graph.  Spoke parities are
    chosen from the component bipartition so every spoke reaches one common
    root; no parity condition on the attachment coordinates is needed.
    """

    b_edges = tuple(tuple(sorted(edge)) for edge in b_edges)
    m_edges = tuple(tuple(sorted(edge)) for edge in m_edges)
    assert check_rfc_direct(n, list(b_edges), list(m_edges), path[0], path[-1]) == (
        True,
        None,
    )
    assert component in off_components(n, b_edges, path)
    component_set = set(component)
    path_set = set(path)
    position = {vertex: index for index, vertex in enumerate(path)}

    attachments = []
    for u, v in b_edges:
        if u in component_set and v in path_set:
            attachments.append((u, v))
        elif v in component_set and u in path_set:
            attachments.append((v, u))
    assert attachments

    local_index = {vertex: index for index, vertex in enumerate(component)}
    q = len(component)
    local_b = [
        tuple(sorted((local_index[u], local_index[v])))
        for u, v in b_edges
        if u in component_set and v in component_set
    ]
    local_m_original = [
        (u, v)
        for u, v in m_edges
        if u in component_set and v in component_set
    ]
    assert local_m_original
    local_m = [
        tuple(sorted((local_index[u], local_index[v])))
        for u, v in local_m_original
    ]
    component_distances = all_dists(q, local_b)
    component_m_distances = tuple(
        component_distances[u][v] for u, v in local_m
    )
    assert all(distance >= 4 and distance % 2 == 0 for distance in component_m_distances)

    # Two-color C.  Put the common root on whichever side minimizes the
    # number of parity corrections.  With K=Delta/2, a spoke has length K or
    # K+1 so that its far endpoint has the chosen root color.  Every spoke is
    # at least K, hence any route through the root has length at least Delta.
    adjacency = adj_masks(q, local_b)
    side = [-1] * q
    side[0] = 0
    stack = [0]
    while stack:
        u = stack.pop()
        neighbors = adjacency[u]
        while neighbors:
            v = (neighbors & -neighbors).bit_length() - 1
            neighbors &= neighbors - 1
            if side[v] < 0:
                side[v] = 1 - side[u]
                stack.append(v)
            else:
                assert side[v] != side[u]
    assert all(value >= 0 for value in side)
    base_length = max(component_m_distances) // 2
    assert base_length >= 2 and 2 * base_length == max(component_m_distances)
    attachment_sides = [side[local_index[component_vertex]] for component_vertex, _ in attachments]
    root_side = min(
        (0, 1),
        key=lambda candidate: sum(
            (base_length % 2) != (endpoint_side ^ candidate)
            for endpoint_side in attachment_sides
        ),
    )
    spoke_lengths = tuple(
        base_length
        if (base_length % 2) == (endpoint_side ^ root_side)
        else base_length + 1
        for endpoint_side in attachment_sides
    )
    assert all(length >= 2 for length in spoke_lengths)
    assert all(2 * length >= max(component_m_distances) for length in spoke_lengths)

    auxiliary_count = sum(length - 1 for length in spoke_lengths)
    root = q + auxiliary_count
    completion_b = list(local_b)
    next_vertex = q
    for (component_vertex, _path_vertex), spoke_length in zip(attachments, spoke_lengths):
        previous = local_index[component_vertex]
        for _ in range(spoke_length - 1):
            completion_b.append(tuple(sorted((previous, next_vertex))))
            previous = next_vertex
            next_vertex += 1
        completion_b.append(tuple(sorted((previous, root))))
    assert next_vertex == root
    order = root + 1
    assert len(set(completion_b)) == len(completion_b)
    assert _is_bipartite_connected(order, completion_b)
    assert union_triangle_free(order, completion_b, local_m)

    completion_distances = all_dists(order, completion_b)
    completion_m_distances = tuple(
        completion_distances[u][v] for u, v in local_m
    )
    assert completion_m_distances == component_m_distances
    ambient_distances = all_dists(n, list(b_edges))
    ambient_m_distances = tuple(
        ambient_distances[u][v] for u, v in local_m_original
    )
    assert all(
        ambient <= completed
        for ambient, completed in zip(ambient_m_distances, completion_m_distances)
    )

    # Exact S2 reproduction.  The mathematical proof does not enumerate:
    # for a cut with the new root outside, each spoke incident to a C-vertex
    # in T crosses at least once, reproducing a_C(T); root-inside follows by
    # complement.  Enumeration is retained as an adversarial check.
    minimum_cut_slack = 0
    if check_all_completion_cuts:
        bit = xor_bits(order)
        slack = slack_array(order, completion_b, local_m, bit)
        minimum_cut_slack = int(slack.min())
        assert minimum_cut_slack >= 0
    return BoundaryCompletion(
        component=component,
        attachments=tuple(attachments),
        spoke_lengths=spoke_lengths,
        order=order,
        b_edges=tuple(completion_b),
        m_edges=tuple(local_m),
        root=root,
        ambient_m_distances=ambient_m_distances,
        component_m_distances=component_m_distances,
        completion_m_distances=completion_m_distances,
        minimum_cut_slack=minimum_cut_slack,
    )
