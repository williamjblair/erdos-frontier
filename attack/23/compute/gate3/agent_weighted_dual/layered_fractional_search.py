"""Heuristic search for a counterexample to the fractional BF-RL relaxation.

The supply graphs have a fixed root/stub corridor and BFS layering, so the
root/stub distance is exact.  Every accepted graph is checked for a fully
nonbridge corridor.  Floating point is discovery-only.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
from compute23.gate3.agent_weighted_dual.explore_bf import bridges  # noqa: E402
from compute23.gate3.rl_lib import all_dists, m_candidates, rl_rhs  # noqa: E402


def build_graph(rng: random.Random, s: int, d: int) -> tuple[int, list[tuple[int, int]]]:
    n = d + 1 + s
    levels = list(range(d + 1))
    extra_levels = [rng.randint(1, d - 1) for _ in range(s)]
    levels.extend(extra_levels)
    edges = {(i, i + 1) for i in range(d)}
    possible = [
        (u, v)
        for u in range(n)
        for v in range(u + 1, n)
        if abs(levels[u] - levels[v]) == 1 and (u, v) not in edges
    ]
    probability = rng.uniform(0.18, 0.72)
    for edge in possible:
        if rng.random() < probability:
            edges.add(edge)
    # Force every extra vertex to have a neighbor one level toward the root
    # and one level toward the stub whenever possible.
    for v in range(d + 1, n):
        lo = [u for u in range(n) if levels[u] == levels[v] - 1]
        hi = [u for u in range(n) if levels[u] == levels[v] + 1]
        if lo:
            edges.add(tuple(sorted((v, rng.choice(lo)))))
        if hi:
            edges.add(tuple(sorted((v, rng.choice(hi)))))
    return n, sorted(edges)


def optimum(n: int, edges: list[tuple[int, int]], d: int):
    dist = all_dists(n, edges)
    if dist[0][d] != d:
        return None
    candidates = m_candidates(n, dist)
    if len(candidates) < 2:
        return None
    masks = np.arange(1 << (n - 1), dtype=np.uint32)
    vertices = list(range(1, n))
    bit = {0: np.zeros(len(masks), dtype=np.int8)}
    for j, v in enumerate(vertices):
        bit[v] = ((masks >> j) & 1).astype(np.int8)
    bound = np.zeros(len(masks), dtype=np.int16)
    for u, v in edges:
        bound += bit[u] ^ bit[v]
    bound -= bit[d]
    columns = np.column_stack([bit[u] ^ bit[v] for u, v in candidates])
    columns = np.vstack([columns, -np.ones((1, len(candidates)), dtype=np.int8)])
    bound = np.append(bound, -2)
    cost = np.asarray([(dist[u][v] + 1) ** 2 for u, v in candidates], float)
    result = linprog(
        -cost,
        A_ub=columns,
        b_ub=bound,
        bounds=[(0, None)] * len(candidates),
        method="highs",
    )
    if result.status == 2:
        return None
    assert result.success
    support = tuple(
        (candidates[i], dist[candidates[i][0]][candidates[i][1]], float(x))
        for i, x in enumerate(result.x)
        if x > 1e-8
    )
    return -float(result.fun), support


def main(seed: int, trials: int, s: int, d: int) -> None:
    rng = random.Random(seed)
    best = None
    accepted = 0
    for trial in range(trials):
        n, edges = build_graph(rng, s, d)
        blocked = bridges(n, edges)
        if any((i, i + 1) in blocked for i in range(d)):
            continue
        result = optimum(n, edges, d)
        if result is None:
            continue
        accepted += 1
        value, support = result
        budget = rl_rhs(n, d)
        ratio = value / budget
        if best is None or ratio > best[0]:
            best = (ratio, value, budget, tuple(edges), support)
            print("BEST", best, flush=True)
        if value > budget + 1e-7:
            print("VIOLATION", best, flush=True)
            return
    print("DONE", accepted, best)


if __name__ == "__main__":
    main(*map(int, sys.argv[1:5]))
