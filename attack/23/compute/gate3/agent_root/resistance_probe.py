"""Discovery-only probe for a rooted effective-resistance certificate.

For a connected bipartite supply graph B and a root/stub pair, test the
pointwise sufficient condition

  max_e (dist_B(e)+1)^2 / R_B(e) * (n-1-R_B(w,x0)) <= rlBudget(s,d)

over every legal same-side pair e.  Foster plus RFC would make this condition
imply the RL inequality.  Floating point is used only to falsify the route;
no output is a proof dependency.
"""

from __future__ import annotations

import argparse
import random

import numpy as np

from compute23.gate3.agent_weighted_dual.explore_bf import (
    bridges,
    connected,
    geodesic_avoiding_bridges,
    random_bipartite,
)
from compute23.gate3.rl_lib import (
    all_dists,
    m_candidates,
    p_of_d,
    rl_rhs,
    slack_array,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


def resistance_matrix(n: int, edges: list[tuple[int, int]]) -> np.ndarray:
    lap = np.zeros((n, n), dtype=float)
    for u, v in edges:
        lap[u, u] += 1.0
        lap[v, v] += 1.0
        lap[u, v] -= 1.0
        lap[v, u] -= 1.0
    pinv = np.linalg.pinv(lap, hermitian=True)
    diag = np.diag(pinv)
    return diag[:, None] + diag[None, :] - 2.0 * pinv


def search(seed: int, trials: int, n: int) -> None:
    rng = random.Random(seed)
    checked = 0
    worst = None
    for _ in range(trials):
        edges = random_bipartite(rng, n, rng.choice((0.12, 0.16, 0.20, 0.25, 0.33)))
        if not edges or not connected(n, edges):
            continue
        dist = all_dists(n, edges)
        candidates = m_candidates(n, dist)
        if not candidates:
            continue
        bits = xor_bits(n)
        pair_validity = {}
        for pair in candidates:
            if union_triangle_free(n, edges, (pair,)):
                pair_validity[pair] = valid_stub_pairs(
                    n, slack_array(n, edges, (pair,), bits)
                )
        resistance = resistance_matrix(n, edges)
        blocked = bridges(n, edges)
        for w in range(n):
            for x0 in range(n):
                if w == x0:
                    continue
                d = dist[w][x0]
                s = n - 1 - d
                p = p_of_d(d)
                if not (5 <= s and d < 2 * s and 2 * s * p < (d + 1) ** 2):
                    continue
                if geodesic_avoiding_bridges(n, edges, dist, w, x0) is None:
                    continue
                reserve = n - 1 - resistance[w, x0]
                ratios = [
                    ((dist[u][v] + 1) ** 2 / resistance[u, v], (u, v))
                    for u, v in candidates
                    if (u, v) in pair_validity and pair_validity[(u, v)][w][x0]
                ]
                if not ratios:
                    continue
                coefficient, pair = max(ratios)
                lhs = coefficient * reserve
                budget = rl_rhs(n, d)
                ratio = lhs / budget
                checked += 1
                if worst is None or ratio > worst[0]:
                    worst = (ratio, edges, w, x0, d, s, pair, coefficient, reserve, budget)
                if ratio > 1.0 + 1e-7:
                    print("FAIL", worst)
                    return
    print("DONE", checked, "worst", worst)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("seed", type=int)
    parser.add_argument("trials", type=int)
    parser.add_argument("n", type=int)
    args = parser.parse_args()
    search(args.seed, args.trials, args.n)
