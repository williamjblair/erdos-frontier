#!/usr/bin/env python3
"""Exact random falsification probe for the two-demand joint estimate.

Every accepted record is checked against all ``2^n`` cuts with integer
arithmetic.  Randomness is used only to generate candidate bipartite supply
graphs and candidate demand pairs; it is never used to decide validity.

The estimate under test is the graph-theoretic input isolated by
``twoEvenCosts_le_rlBudget_of_jointDistanceSum``::

    D1 + D2 <= n + p(dist(w, x0)) - 2.

Here the two internal demands have even supply distance at least four and the
rooted cut condition is exact.  The report keeps the largest signed gap for
each root--stub distance and separately counts the genuinely open subcase in
which both internal distances are at least six.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
import random

import numpy as np

from compute23.gate2.common import adj_masks, bfs_dist
from compute23.gate3.rl_lib import (
    all_dists,
    p_of_d,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


Edge = tuple[int, int]


def connected_bipartite_graph(rng: random.Random, n: int) -> list[Edge]:
    """Generate a connected bipartite graph, usually sparse and long."""

    order = list(range(n))
    rng.shuffle(order)
    edges: set[Edge] = set()

    # A random recursive tree guarantees connectedness.  Its unique
    # two-colouring then fixes which additional edges preserve bipartiteness.
    for index in range(1, n):
        parent_index = rng.randrange(index)
        u, v = order[index], order[parent_index]
        edges.add(tuple(sorted((u, v))))

    adjacency = adj_masks(n, list(edges))
    colour = [-1] * n
    colour[0] = 0
    queue = [0]
    for u in queue:
        neighbors = adjacency[u]
        while neighbors:
            v = (neighbors & -neighbors).bit_length() - 1
            neighbors &= neighbors - 1
            if colour[v] < 0:
                colour[v] = 1 - colour[u]
                queue.append(v)

    cross_pairs = [
        (u, v)
        for u in range(n)
        for v in range(u + 1, n)
        if colour[u] != colour[v] and (u, v) not in edges
    ]
    # Bias strongly toward the sparse region where long demands exist, while
    # still sampling a few denser supplies.
    density = rng.choice((0.0, 0.03, 0.06, 0.10, 0.16, 0.24))
    edges.update(edge for edge in cross_pairs if rng.random() < density)
    return sorted(edges)


def candidate_demands(n: int, distances: list[list[int]]) -> list[Edge]:
    return [
        (u, v)
        for u in range(n)
        for v in range(u + 1, n)
        if distances[u][v] >= 4 and distances[u][v] % 2 == 0
    ]


def run(
    *, nlo: int, nhi: int, trials: int, pairs_per_graph: int, seed: int
) -> dict[str, object]:
    rng = random.Random(seed)
    bits = {n: xor_bits(n) for n in range(nlo, nhi + 1)}
    counts: Counter[str] = Counter()
    best_by_d: dict[int, tuple[int, object]] = {}
    best_open_by_d: dict[int, tuple[int, object]] = {}
    best_unrooted_excess: tuple[int, object] | None = None
    best_twice_slack_excess: tuple[int, object] | None = None
    best_strict_weighted_excess: tuple[int, object] | None = None
    first_failure = None

    for _ in range(trials):
        n = rng.randint(nlo, nhi)
        b_edges = connected_bipartite_graph(rng, n)
        adjacency = adj_masks(n, b_edges)
        assert all(value >= 0 for value in bfs_dist(n, adjacency, 0))
        distances = all_dists(n, b_edges)
        candidates = candidate_demands(n, distances)
        if len(candidates) < 2:
            continue

        pairs = list(combinations(candidates, 2))
        if len(pairs) > pairs_per_graph:
            # Long pairs are most likely to challenge the estimate.  Retain
            # half of the sample from the longest-distance prefix and half
            # uniformly from the whole exact candidate set.
            pairs.sort(
                key=lambda pair: sum(distances[u][v] for u, v in pair),
                reverse=True,
            )
            long_count = pairs_per_graph // 2
            chosen = pairs[:long_count]
            chosen.extend(rng.sample(pairs[long_count:], pairs_per_graph - long_count))
            pairs = chosen

        supply = np.zeros(1 << n, dtype=np.int16)
        for u, v in b_edges:
            supply += bits[n][u] ^ bits[n][v]
        demand_cut = {
            edge: bits[n][edge[0]] ^ bits[n][edge[1]] for edge in candidates
        }

        for demands in pairs:
            counts["pairs_sampled"] += 1
            if not union_triangle_free(n, b_edges, demands):
                continue
            slack = supply - demand_cut[demands[0]] - demand_cut[demands[1]]
            if int(slack.min()) < 0:
                continue
            counts["unrooted_valid"] += 1
            roots = valid_stub_pairs(n, slack)
            demand_distances = tuple(distances[u][v] for u, v in demands)
            unrooted_excess = sum(demand_distances) - n
            unrooted_witness = {
                "n": n,
                "b_edges": tuple(b_edges),
                "demands": demands,
                "demand_distances": demand_distances,
                "lhs": sum(demand_distances),
                "rhs_n": n,
            }
            if (
                best_unrooted_excess is None
                or unrooted_excess > best_unrooted_excess[0]
            ):
                best_unrooted_excess = (unrooted_excess, unrooted_witness)
            for root in range(n):
                for stub in range(n):
                    if not roots[root][stub]:
                        continue
                    counts["rooted_valid"] += 1
                    d = distances[root][stub]
                    rhs = n + p_of_d(d) - 2
                    gap = sum(demand_distances) - rhs
                    witness = {
                        "n": n,
                        "b_edges": tuple(b_edges),
                        "demands": demands,
                        "demand_distances": demand_distances,
                        "root": root,
                        "stub": stub,
                        "root_distance": d,
                        "lhs": sum(demand_distances),
                        "rhs": rhs,
                    }
                    twice_slack_excess = sum(demand_distances) - 2 * (
                        n - 1 - d
                    )
                    if (
                        best_twice_slack_excess is None
                        or twice_slack_excess > best_twice_slack_excess[0]
                    ):
                        best_twice_slack_excess = (
                            twice_slack_excess,
                            witness,
                        )
                    if d >= 3:
                        lo, hi = sorted(demand_distances)
                        strict_weighted_excess = lo + 2 * hi - 2 * (n - 2)
                        strict_witness = {
                            **witness,
                            "weighted_lhs": lo + 2 * hi,
                            "strict_weighted_rhs": 2 * (n - 2),
                        }
                        if (
                            best_strict_weighted_excess is None
                            or strict_weighted_excess
                            > best_strict_weighted_excess[0]
                        ):
                            best_strict_weighted_excess = (
                                strict_weighted_excess,
                                strict_witness,
                            )
                    if d not in best_by_d or gap > best_by_d[d][0]:
                        best_by_d[d] = (gap, witness)
                    if min(demand_distances) >= 6:
                        counts["both_at_least_six"] += 1
                        if d not in best_open_by_d or gap > best_open_by_d[d][0]:
                            best_open_by_d[d] = (gap, witness)
                    if gap > 0:
                        counts["joint_failures"] += 1
                        if first_failure is None:
                            first_failure = witness

    return {
        "parameters": {
            "nlo": nlo,
            "nhi": nhi,
            "trials": trials,
            "pairs_per_graph": pairs_per_graph,
            "seed": seed,
        },
        "counts": dict(counts),
        "best_gap_by_root_distance": {
            d: record for d, record in sorted(best_by_d.items())
        },
        "best_open_gap_by_root_distance": {
            d: record for d, record in sorted(best_open_by_d.items())
        },
        "best_unrooted_excess_over_n": best_unrooted_excess,
        "best_excess_over_twice_slack": best_twice_slack_excess,
        "best_strict_weighted_excess": best_strict_weighted_excess,
        "first_failure": first_failure,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nlo", type=int, default=10)
    parser.add_argument("--nhi", type=int, default=16)
    parser.add_argument("--trials", type=int, default=2000)
    parser.add_argument("--pairs-per-graph", type=int, default=24)
    parser.add_argument("--seed", type=int, default=230617)
    args = parser.parse_args()
    print(run(**vars(args)))


if __name__ == "__main__":
    main()
