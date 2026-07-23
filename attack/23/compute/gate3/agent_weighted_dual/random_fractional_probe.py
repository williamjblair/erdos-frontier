"""Discovery-only random probe of the unboxed fractional RFC relaxation."""

from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from compute23.gate3.agent_root.dual_probe import fractional_optimum
from compute23.gate3.rl_lib import all_dists, m_candidates, p_of_d, rl_rhs


def connected(n: int, edges: list[tuple[int, int]]) -> bool:
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = {0}
    stack = [0]
    while stack:
        for v in adj[stack.pop()]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def random_bipartite(
    rng: random.Random, n: int, probability: float
) -> list[tuple[int, int]]:
    split = rng.randint(2, n - 2)
    order = list(range(n))
    rng.shuffle(order)
    left, right = order[:split], order[split:]
    return sorted(
        (min(u, v), max(u, v))
        for u in left
        for v in right
        if rng.random() < probability
    )


def main(seed: int, trials: int, nlo: int, nhi: int) -> None:
    rng = random.Random(seed)
    checked = 0
    best = None
    for trial in range(trials):
        n = rng.randint(nlo, nhi)
        edges = random_bipartite(
            rng, n, rng.choice((0.10, 0.14, 0.18, 0.24, 0.32, 0.45))
        )
        if not edges or not connected(n, edges):
            continue
        dist = all_dists(n, edges)
        candidates = m_candidates(n, dist)
        if len(candidates) < 2:
            continue
        pairs = []
        for w in range(n):
            for x in range(w + 1, n):
                d = dist[w][x]
                s = n - 1 - d
                if (
                    5 <= s
                    and d <= 2 * s
                    and 2 * s * p_of_d(d) < (d + 1) ** 2
                ):
                    pairs.append((w, x))
        rng.shuffle(pairs)
        for w, x in pairs[:3]:
            optimum = fractional_optimum(
                n, edges, candidates, dist, w, x, box=False
            )
            if optimum is None:
                continue
            value, result = optimum
            checked += 1
            budget = rl_rhs(n, dist[w][x])
            ratio = value / budget
            data = (ratio, n, tuple(edges), w, x, dist[w][x], value, budget,
                    tuple((candidates[i], dist[candidates[i][0]][candidates[i][1]], float(z))
                          for i, z in enumerate(result.x) if z > 1e-8))
            if best is None or ratio > best[0]:
                best = data
                print("BEST", data, flush=True)
            if value > budget + 1e-7:
                print("VIOLATION", data, flush=True)
                return
    print("DONE", checked, "best", best)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:5]))
