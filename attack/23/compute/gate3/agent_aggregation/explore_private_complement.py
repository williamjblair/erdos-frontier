"""Deterministic exact random audit of the private-completion complement.

Discovery only; no random statement is a proof dependency.  All accepted
instances, RFC checks, bridge checks, distances, and budgets use exact
integer/Boolean arithmetic.  The PRNG seed merely makes the sample corpus
reproducible.
"""

from __future__ import annotations

import random

import numpy as np

from compute23.gate2.common import adj_masks, bfs_dist
from compute23.gate3.rl_lib import (
    all_dists,
    m_candidates,
    p_of_d,
    rl_rhs,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)

from compute23.gate3.agent_aggregation.quotient_cut_average import canonical_geodesic
from compute23.gate3.agent_aggregation.distance_four_completion import (
    minimum_proper_edge_coloring,
)
from compute23.gate3.agent_aggregation.distance_multiset_completion import (
    multiset_completion_order,
)


def random_bipartite(rng: random.Random, n: int) -> list[tuple[int, int]]:
    n_left = rng.randint(1, n - 1)
    vertices = list(range(n))
    rng.shuffle(vertices)
    left, right = vertices[:n_left], vertices[n_left:]
    probability = rng.choice([0.15, 0.25, 0.35, 0.5])
    return sorted(
        {
            tuple(sorted((u, v)))
            for u in left
            for v in right
            if rng.random() < probability
        }
    )


def connected_without_edge(n, edges, removed) -> bool:
    adjacency = adj_masks(
        n, [edge for edge in edges if tuple(sorted(edge)) != tuple(sorted(removed))]
    )
    return all(distance >= 0 for distance in bfs_dist(n, adjacency, 0))


def canonical_path_is_all_nonbridge(n, edges, path) -> bool:
    return all(
        connected_without_edge(n, edges, edge)
        for edge in zip(path, path[1:])
    )


def run_audit(trials: int = 3000, seed: int = 230711) -> dict[str, object]:
    rng = random.Random(seed)
    counts = {
        "m_sets": 0,
        "rooted": 0,
        "residual": 0,
        "bridge_free": 0,
        "private_closed": 0,
        "private_complement": 0,
        "distance_four_shared_closed": 0,
        "combined_complement": 0,
        "multiset_closed": 0,
        "multiset_complement": 0,
        "multiset_linear_bound_pass": 0,
        "multiset_linear_bound_fail": 0,
        "multiset_linear_plus_one_fail": 0,
        "top_two_distance_sum_fail": 0,
        "top_two_joint_bound_fail": 0,
        "top_two_distance_sum_equality": 0,
    }
    complement_profiles = set()
    linear_failure_profiles = set()
    for _ in range(trials):
        n = rng.randint(14, 16)
        b_edges = random_bipartite(rng, n)
        if not b_edges:
            continue
        adjacency = adj_masks(n, b_edges)
        if any(distance < 0 for distance in bfs_dist(n, adjacency, 0)):
            continue
        distances = all_dists(n, b_edges)
        candidates = m_candidates(n, distances)
        if len(candidates) < 2:
            continue
        bit = xor_bits(n)
        supply = np.zeros(1 << n, dtype=np.int32)
        for u, v in b_edges:
            supply += bit[u] ^ bit[v]
        for _ in range(4):
            size = rng.randint(2, min(4, len(candidates)))
            m_edges = tuple(sorted(rng.sample(candidates, size)))
            if not union_triangle_free(n, b_edges, m_edges):
                continue
            slack = supply.copy()
            for u, v in m_edges:
                slack -= bit[u] ^ bit[v]
            if slack.min() < 0:
                continue
            counts["m_sets"] += 1
            valid = valid_stub_pairs(n, slack)
            m_distances = tuple(distances[u][v] for u, v in m_edges)
            endpoint_count = len({vertex for edge in m_edges for vertex in edge})
            private_order = endpoint_count + sum(distance - 1 for distance in m_distances)
            multiset_order = multiset_completion_order(m_distances)
            gamma = sum((distance + 1) ** 2 for distance in m_distances)
            for root in range(n):
                for stub in range(n):
                    if not valid[root][stub]:
                        continue
                    counts["rooted"] += 1
                    d = distances[root][stub]
                    s = n - 1 - d
                    if not (
                        s >= 5
                        and d <= 2 * s
                        and 2 * s * p_of_d(d) < (d + 1) ** 2
                    ):
                        continue
                    counts["residual"] += 1
                    path = canonical_geodesic(n, b_edges, root, stub)
                    if not canonical_path_is_all_nonbridge(n, b_edges, path):
                        continue
                    counts["bridge_free"] += 1
                    budget = rl_rhs(n, d)
                    if multiset_order**2 <= budget:
                        counts["multiset_closed"] += 1
                    else:
                        counts["multiset_complement"] += 1
                    if multiset_order <= s + p_of_d(d):
                        counts["multiset_linear_bound_pass"] += 1
                    else:
                        counts["multiset_linear_bound_fail"] += 1
                        linear_failure_profiles.add(
                            (
                                n,
                                d,
                                s,
                                tuple(sorted(m_distances)),
                                multiset_order,
                                s + p_of_d(d),
                                budget,
                            )
                        )
                    if multiset_order > s + p_of_d(d) + 1:
                        counts["multiset_linear_plus_one_fail"] += 1
                    if sum(sorted(m_distances, reverse=True)[:2]) > 2 * s:
                        counts["top_two_distance_sum_fail"] += 1
                    if sum(sorted(m_distances, reverse=True)[:2]) == 2 * s:
                        counts["top_two_distance_sum_equality"] += 1
                    if sum(sorted(m_distances, reverse=True)[:2]) > (
                        s + d + p_of_d(d) - 1
                    ):
                        counts["top_two_joint_bound_fail"] += 1
                    if private_order**2 <= budget:
                        counts["private_closed"] += 1
                    else:
                        counts["private_complement"] += 1
                        shared_order = None
                        if set(m_distances) == {4}:
                            edge_colors = minimum_proper_edge_coloring(m_edges)
                            shared_order = 2 * endpoint_count + len(set(edge_colors))
                            if shared_order**2 <= budget:
                                counts["distance_four_shared_closed"] += 1
                            else:
                                counts["combined_complement"] += 1
                        else:
                            counts["combined_complement"] += 1
                        complement_profiles.add(
                            (
                                n,
                                d,
                                s,
                                len(m_edges),
                                tuple(sorted(m_distances)),
                                endpoint_count,
                                private_order,
                                gamma,
                                budget,
                                shared_order,
                            )
                        )
    return {
        "trials": trials,
        "seed": seed,
        "counts": counts,
        "complement_profiles": tuple(sorted(complement_profiles)),
        "linear_failure_profiles": tuple(sorted(linear_failure_profiles)),
    }


if __name__ == "__main__":
    print(run_audit())
