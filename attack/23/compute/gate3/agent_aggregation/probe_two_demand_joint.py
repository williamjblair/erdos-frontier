#!/usr/bin/env python3
"""Exact small-corpus probe for the now-falsified joint distance bound.

The formerly conjectured structural form was

    D1 + D2 <= n,

with equality forcing every RFC-admissible positive root--stub distance to
be even.  For d >= 3 this implies

    D1 + D2 <= n + partnerDistance(d) - 2.

The all-nonbridge ``n=76`` diamond-chain fixture in
``agent_weighted_dual/joint_distance_counterexample.py`` disproves this
bound.  This script remains only as a regression record of why exhaustive
orders through nine looked deceptively positive.  The overlap formulation
is checked on one exact geodesic per demand; its numerical excess is
path-independent by inclusion--exclusion.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations

import numpy as np

from compute23.gate2.common import adj_masks, parse_graph6
from compute23.gate3.rl_lib import (
    all_dists,
    gen_bipartite,
    geodesics_between,
    m_candidates,
    p_of_d,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


def run(nmax: int) -> dict[str, object]:
    counts: Counter[str] = Counter()
    first: dict[str, object] = {}
    equality_distance_parities: Counter[tuple[int, int]] = Counter()
    excess_distance_profiles: Counter[tuple[int, int]] = Counter()

    for n in range(5, nmax + 1):
        bits = xor_bits(n)
        for graph6 in gen_bipartite(n):
            nn, b_edges = parse_graph6(graph6)
            assert nn == n
            distances = all_dists(n, b_edges)
            adjacency = adj_masks(n, b_edges)
            candidates = m_candidates(n, distances)
            if len(candidates) < 2:
                continue
            supply = np.zeros(1 << n, dtype=np.int16)
            for u, v in b_edges:
                supply += bits[u] ^ bits[v]
            demand_cuts = {
                edge: bits[edge[0]] ^ bits[edge[1]] for edge in candidates
            }

            for demands in combinations(candidates, 2):
                if not union_triangle_free(n, b_edges, demands):
                    continue
                slack = supply.copy()
                for edge in demands:
                    slack -= demand_cuts[edge]
                if int(slack.min()) < 0:
                    continue
                counts["unrooted_valid"] += 1
                demand_distances = tuple(
                    distances[u][v] for u, v in demands
                )
                distance_sum = sum(demand_distances)
                if distance_sum > n:
                    counts["unrooted_sum_gt_n"] += 1
                    first.setdefault(
                        "unrooted_sum_gt_n",
                        (graph6, demands, demand_distances),
                    )
                if distance_sum == n:
                    counts["unrooted_sum_eq_n"] += 1

                paths = [
                    geodesics_between(
                        n,
                        adjacency,
                        distances,
                        u,
                        v,
                    )[0]
                    for u, v in demands
                ]
                vertices_one, vertices_two = map(set, paths)
                overlap = len(vertices_one & vertices_two)
                unused = n - len(vertices_one | vertices_two)
                assert overlap - unused == distance_sum + 2 - n

                valid_roots = valid_stub_pairs(n, slack)
                tight_masks = [mask for mask, value in enumerate(slack) if value == 0]
                tight_signature = {
                    vertex: tuple((mask >> vertex) & 1 for mask in tight_masks)
                    for vertex in range(n)
                }
                atom_size = Counter(tight_signature.values())
                for root in range(n):
                    for stub in range(n):
                        if not valid_roots[root][stub]:
                            continue
                        counts["rooted_valid"] += 1
                        d = distances[root][stub]
                        root_atom_size = atom_size[tight_signature[root]]
                        if distance_sum + root_atom_size > n + 2:
                            counts["atom_size_bound_fail"] += 1
                            first.setdefault(
                                "atom_size_bound_fail",
                                (
                                    graph6,
                                    demands,
                                    root,
                                    stub,
                                    demand_distances,
                                    d,
                                    root_atom_size,
                                ),
                            )
                        if d > 0:
                            excess_distance_profiles[(distance_sum - n, d)] += 1
                        if distance_sum == n and d > 0:
                            equality_distance_parities[(d % 2, d)] += 1
                            if d % 2 == 1:
                                counts["equality_positive_odd_root"] += 1
                                first.setdefault(
                                    "equality_positive_odd_root",
                                    (graph6, demands, root, stub, demand_distances, d),
                                )
                        if d < 3:
                            continue
                        counts["rooted_d_ge_three"] += 1
                        partner = p_of_d(d)
                        joint_rhs = n + partner - 2
                        overlap_rhs = unused + partner
                        assert (
                            distance_sum <= joint_rhs
                        ) == (overlap <= overlap_rhs)
                        if distance_sum > joint_rhs:
                            counts["joint_bound_fail"] += 1
                            first.setdefault(
                                "joint_bound_fail",
                                (graph6, demands, root, stub, demand_distances, d),
                            )

    return {
        "nmax": nmax,
        "counts": dict(counts),
        "equality_distance_parities": dict(equality_distance_parities),
        "excess_distance_profiles": dict(excess_distance_profiles),
        "first": first,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmax", type=int, default=9)
    args = parser.parse_args()
    print(run(args.nmax))


if __name__ == "__main__":
    main()
