"""Adversarial exact search for the multiset-completion size-gate complement.

Discovery only.  Every retained M set is checked by its exact all-cuts slack
array; every rooted pair comes from the exact zero-cut criterion; every BF
path is checked edge by edge.  Randomness only selects candidate graphs and
candidate insertion order.
"""

from __future__ import annotations

import random
from collections import defaultdict

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
from compute23.gate3.agent_aggregation.distance_multiset_completion import (
    multiset_completion_order,
)
from compute23.gate3.agent_aggregation.explore_private_complement import (
    canonical_path_is_all_nonbridge,
    random_bipartite,
)
from compute23.gate3.agent_aggregation.quotient_cut_average import canonical_geodesic


def _greedy_feasible_m(
    rng: random.Random,
    *,
    n: int,
    candidates: list[tuple[int, int]],
    distances: list[list[int]],
    supply: np.ndarray,
    bit: list[np.ndarray],
    target_size: int,
    mode: str,
) -> tuple[tuple[tuple[int, int], ...], np.ndarray] | None:
    by_distance: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for edge in candidates:
        by_distance[distances[edge[0]][edge[1]]].append(edge)
    available_distances = [distance for distance, edges in by_distance.items() if edges]
    if not available_distances:
        return None
    if mode == "repeated":
        selected_distances = [rng.choice(available_distances)]
    elif mode == "mixed" and len(available_distances) >= 2:
        selected_distances = rng.sample(available_distances, 2)
    else:
        selected_distances = available_distances
    pool = [edge for distance in selected_distances for edge in by_distance[distance]]
    rng.shuffle(pool)
    chosen: list[tuple[int, int]] = []
    slack = supply.copy()
    for edge in pool:
        if len(chosen) == target_size:
            break
        trial = tuple(chosen + [edge])
        if not union_triangle_free(n, [], trial):
            # This checks M-triangles.  B-related triangles are impossible for
            # distance-at-least-four candidates.
            continue
        edge_cross = bit[edge[0]] ^ bit[edge[1]]
        if int((slack - edge_cross).min()) < 0:
            continue
        slack -= edge_cross
        chosen.append(edge)
    if len(chosen) < 2:
        return None
    assert int(slack.min()) >= 0
    return tuple(sorted(chosen)), slack


def run_search(
    *,
    trials: int = 1200,
    seed: int = 230713,
    n_min: int = 14,
    n_max: int = 18,
    max_m: int = 8,
) -> dict[str, object]:
    rng = random.Random(seed)
    counts = {
        "connected_B": 0,
        "feasible_M": 0,
        "rooted": 0,
        "strict_residual": 0,
        "bridge_free": 0,
        "multiset_closed": 0,
        "multiset_complement": 0,
        "rl_violations": 0,
        "linear_plus_one_fail": 0,
        "top_two_distance_sum_fail": 0,
        "top_two_joint_bound_fail": 0,
        "top_two_distance_sum_equality": 0,
    }
    first_complement = None
    worst_margin = None
    for _ in range(trials):
        n = rng.randint(n_min, n_max)
        b_edges = random_bipartite(rng, n)
        if not b_edges:
            continue
        adjacency = adj_masks(n, b_edges)
        if any(distance < 0 for distance in bfs_dist(n, adjacency, 0)):
            continue
        counts["connected_B"] += 1
        distances = all_dists(n, b_edges)
        candidates = m_candidates(n, distances)
        if len(candidates) < 2:
            continue
        bit = xor_bits(n)
        supply = np.zeros(1 << n, dtype=np.int32)
        for u, v in b_edges:
            supply += bit[u] ^ bit[v]
        for mode in ("repeated", "mixed", "random"):
            target = rng.randint(2, min(max_m, len(candidates)))
            built = _greedy_feasible_m(
                rng,
                n=n,
                candidates=candidates,
                distances=distances,
                supply=supply,
                bit=bit,
                target_size=target,
                mode=mode,
            )
            if built is None:
                continue
            m_edges, slack = built
            if not union_triangle_free(n, b_edges, m_edges):
                continue
            counts["feasible_M"] += 1
            valid = valid_stub_pairs(n, slack)
            demand_distances = tuple(distances[u][v] for u, v in m_edges)
            completion_order = multiset_completion_order(demand_distances)
            gamma = sum((distance + 1) ** 2 for distance in demand_distances)
            for root in range(n):
                for stub in range(n):
                    if not valid[root][stub]:
                        continue
                    counts["rooted"] += 1
                    d = distances[root][stub]
                    s = n - 1 - d
                    if not (
                        n >= 14
                        and len(m_edges) >= 2
                        and s >= 5
                        and d < 2 * s
                        and 2 * s * p_of_d(d) < (d + 1) ** 2
                    ):
                        continue
                    counts["strict_residual"] += 1
                    path = canonical_geodesic(n, b_edges, root, stub)
                    if not canonical_path_is_all_nonbridge(n, b_edges, path):
                        continue
                    counts["bridge_free"] += 1
                    budget = rl_rhs(n, d)
                    if gamma > budget:
                        counts["rl_violations"] += 1
                    if completion_order > s + p_of_d(d) + 1:
                        counts["linear_plus_one_fail"] += 1
                    if sum(sorted(demand_distances, reverse=True)[:2]) > 2 * s:
                        counts["top_two_distance_sum_fail"] += 1
                    if sum(sorted(demand_distances, reverse=True)[:2]) == 2 * s:
                        counts["top_two_distance_sum_equality"] += 1
                    if sum(sorted(demand_distances, reverse=True)[:2]) > (
                        s + d + p_of_d(d) - 1
                    ):
                        counts["top_two_joint_bound_fail"] += 1
                    margin = budget - completion_order**2
                    profile = {
                        "n": n,
                        "d": d,
                        "s": s,
                        "m": len(m_edges),
                        "distances": tuple(sorted(demand_distances)),
                        "gamma": gamma,
                        "budget": budget,
                        "completion_order": completion_order,
                        "margin": margin,
                        "b_edges": tuple(b_edges),
                        "m_edges": m_edges,
                        "root": root,
                        "stub": stub,
                        "path": path,
                    }
                    if worst_margin is None or margin < worst_margin["margin"]:
                        worst_margin = profile
                    if margin >= 0:
                        counts["multiset_closed"] += 1
                    else:
                        counts["multiset_complement"] += 1
                        if first_complement is None:
                            first_complement = profile
    return {
        "trials": trials,
        "seed": seed,
        "n_range": (n_min, n_max),
        "max_m": max_m,
        "counts": counts,
        "first_complement": first_complement,
        "worst_margin": worst_margin,
    }


if __name__ == "__main__":
    print(run_search())
