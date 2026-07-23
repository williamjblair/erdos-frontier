"""Exact 1-sum completion depending only on the demand-distance multiset."""

from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from math import isqrt

from compute23.gate3.rl_lib import all_dists, slack_array, union_triangle_free, xor_bits


Edge = tuple[int, int]


def ceil_sqrt(value: int) -> int:
    assert value >= 0
    root = isqrt(value)
    return root if root * root == value else root + 1


def multiset_completion_order(distances: tuple[int, ...] | list[int]) -> int:
    """Order of the articulation 1-sum of balanced odd-cycle blocks."""

    distances = tuple(distances)
    assert distances and all(distance >= 4 and distance % 2 == 0 for distance in distances)
    return 1 + sum(
        (distance + 1) * ceil_sqrt(multiplicity) - 1
        for distance, multiplicity in Counter(distances).items()
    )


@dataclass(frozen=True)
class DistanceMultisetCompletion:
    order: int
    b_edges: tuple[Edge, ...]
    m_edges: tuple[Edge, ...]
    requested_distances: tuple[int, ...]
    completion_distances: tuple[int, ...]
    block_orders: tuple[int, ...]
    block_multiplicities: tuple[int, ...]
    minimum_cut_slack: int | None


def build_distance_multiset_completion(
    distances: tuple[int, ...] | list[int],
    *,
    check_all_cuts: bool = True,
) -> DistanceMultisetCompletion:
    """Build a valid instance with precisely the requested cost multiset.

    For distance ``D`` of multiplicity ``m``, take ``C_{D+1}[q]`` with
    ``q=ceil(sqrt(m))`` under its standard maximum cut and retain any ``m``
    of the ``q^2`` monochromatic edges.  Blocks are 1-summed by identifying a
    supply-only vertex in cluster one.
    """

    requested = tuple(sorted(distances))
    assert requested and all(distance >= 4 and distance % 2 == 0 for distance in requested)
    b_edges: list[Edge] = []
    m_edges: list[Edge] = []
    next_vertex = 1
    common_pivot = 0
    block_orders: list[int] = []
    block_multiplicities: list[int] = []

    for distance, multiplicity in sorted(Counter(requested).items()):
        cycle_length = distance + 1
        q = ceil_sqrt(multiplicity)
        block_order = cycle_length * q
        block_orders.append(block_order)
        block_multiplicities.append(multiplicity)

        # Local cluster 1, vertex 0 is the common pivot.  Every other local
        # vertex receives a fresh global label.
        local_to_global: dict[tuple[int, int], int] = {}
        for cluster in range(cycle_length):
            for index in range(q):
                if cluster == 1 and index == 0:
                    local_to_global[(cluster, index)] = common_pivot
                else:
                    local_to_global[(cluster, index)] = next_vertex
                    next_vertex += 1

        # The standard maximum-cut supply graph is the long chain of cluster
        # pairs 0-1-...-D.  The omitted cycle adjacency D-0 is monochromatic.
        for cluster in range(cycle_length - 1):
            for left in range(q):
                for right in range(q):
                    b_edges.append(
                        tuple(
                            sorted(
                                (
                                    local_to_global[(cluster, left)],
                                    local_to_global[(cluster + 1, right)],
                                )
                            )
                        )
                    )

        candidates = [
            tuple(
                sorted(
                    (
                        local_to_global[(0, left)],
                        local_to_global[(cycle_length - 1, right)],
                    )
                )
            )
            for left in range(q)
            for right in range(q)
        ]
        m_edges.extend(candidates[:multiplicity])

    order = next_vertex
    assert order == multiset_completion_order(requested)
    assert len(set(b_edges)) == len(b_edges)
    assert len(set(m_edges)) == len(m_edges)
    assert union_triangle_free(order, b_edges, m_edges)
    distances_matrix = all_dists(order, b_edges)
    completion_distances = tuple(sorted(distances_matrix[u][v] for u, v in m_edges))
    assert completion_distances == requested

    minimum_cut_slack: int | None = None
    if check_all_cuts:
        bit = xor_bits(order)
        slack = slack_array(order, b_edges, m_edges, bit)
        minimum_cut_slack = int(slack.min())
        assert minimum_cut_slack >= 0
    return DistanceMultisetCompletion(
        order=order,
        b_edges=tuple(b_edges),
        m_edges=tuple(m_edges),
        requested_distances=requested,
        completion_distances=completion_distances,
        block_orders=tuple(block_orders),
        block_multiplicities=tuple(block_multiplicities),
        minimum_cut_slack=minimum_cut_slack,
    )
