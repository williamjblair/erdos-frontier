"""Discovery-only search for bridge-free BF-RL instances and cut LPs.

Nothing in this file is a proof dependency.  It emits complete integer
instances so any candidate inequality can subsequently be reproduced exactly.
"""

from __future__ import annotations

import random
import sys
from collections import deque
from itertools import combinations

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, "compute23/gate3")
from rl_lib import (  # noqa: E402
    adj_masks,
    all_dists,
    gamma_of,
    m_candidates,
    p_of_d,
    rl_rhs,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


def connected(n: int, edges: list[tuple[int, int]]) -> bool:
    adj = adj_masks(n, edges)
    seen = {0}
    q = [0]
    while q:
        u = q.pop()
        mask = adj[u]
        while mask:
            bit = mask & -mask
            mask -= bit
            v = bit.bit_length() - 1
            if v not in seen:
                seen.add(v)
                q.append(v)
    return len(seen) == n


def bridges(n: int, edges: list[tuple[int, int]]) -> set[tuple[int, int]]:
    adj: list[list[tuple[int, int]]] = [[] for _ in range(n)]
    for idx, (u, v) in enumerate(edges):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    tin = [-1] * n
    low = [-1] * n
    timer = 0
    out: set[tuple[int, int]] = set()

    def dfs(u: int, parent_edge: int) -> None:
        nonlocal timer
        tin[u] = low[u] = timer
        timer += 1
        for v, idx in adj[u]:
            if idx == parent_edge:
                continue
            if tin[v] >= 0:
                low[u] = min(low[u], tin[v])
            else:
                dfs(v, idx)
                low[u] = min(low[u], low[v])
                if low[v] > tin[u]:
                    out.add(tuple(sorted((u, v))))

    dfs(0, -1)
    return out


def geodesic_avoiding_bridges(
    n: int,
    edges: list[tuple[int, int]],
    dist: list[list[int]],
    w: int,
    x: int,
) -> tuple[int, ...] | None:
    blocked = bridges(n, edges)
    adj = adj_masks(n, edges)
    parent = {w: -1}
    q = deque([w])
    while q:
        u = q.popleft()
        if u == x:
            path = []
            while u >= 0:
                path.append(u)
                u = parent[u]
            return tuple(reversed(path))
        mask = adj[u]
        while mask:
            bit = mask & -mask
            mask -= bit
            v = bit.bit_length() - 1
            if v in parent or tuple(sorted((u, v))) in blocked:
                continue
            if dist[w][v] != dist[w][u] + 1:
                continue
            if dist[w][v] + dist[v][x] != dist[w][x]:
                continue
            parent[v] = u
            q.append(v)
    return None


def random_bipartite(
    rng: random.Random, n: int, q: float
) -> list[tuple[int, int]]:
    split = rng.randint(3, n - 3)
    vertices = list(range(n))
    rng.shuffle(vertices)
    left, right = vertices[:split], vertices[split:]
    return sorted(
        (min(u, v), max(u, v))
        for u in left
        for v in right
        if rng.random() < q
    )


def weighted_cut_dual_optimum(
    n: int,
    edges: list[tuple[int, int]],
    M: tuple[tuple[int, int], ...],
    w: int,
    x: int,
    distances: list[list[int]],
) -> tuple[float, tuple[float, ...]]:
    """Maximum fractionally reweighted Gamma under all rooted cut rows."""

    rows = []
    bounds = []
    # Complement symmetry lets us keep the representative not containing w.
    vertices = [v for v in range(n) if v != w]
    for mask in range(1 << (n - 1)):
        inside = [False] * n
        for j, v in enumerate(vertices):
            inside[v] = bool((mask >> j) & 1)
        cover = [int(inside[u] != inside[v]) for u, v in M]
        if not any(cover):
            continue
        supply = sum(inside[u] != inside[v] for u, v in edges)
        reserve = int(inside[w] != inside[x])
        rows.append(cover)
        bounds.append(supply - reserve)
    costs = np.array(
        [(distances[u][v] + 1) ** 2 for u, v in M], dtype=float
    )
    result = linprog(
        -costs,
        A_ub=np.asarray(rows, dtype=float),
        b_ub=np.asarray(bounds, dtype=float),
        bounds=[(0, None)] * len(M),
        method="highs",
    )
    assert result.success
    return -float(result.fun), tuple(float(y) for y in result.x)


def search(seed: int, trials: int, n: int = 14) -> None:
    rng = random.Random(seed)
    bits = xor_bits(n)
    found: dict[tuple[int, int, tuple[int, ...]], tuple] = {}
    for trial in range(trials):
        edges = random_bipartite(rng, n, rng.choice((0.12, 0.16, 0.20, 0.25)))
        if not edges or not connected(n, edges):
            continue
        dist = all_dists(n, edges)
        candidates = m_candidates(n, dist)
        if len(candidates) < 2:
            continue
        base = np.zeros(1 << n, dtype=np.int16)
        for u, v in edges:
            base += bits[u] ^ bits[v]
        for _ in range(20):
            size = rng.randint(2, min(5, len(candidates)))
            M = tuple(sorted(rng.sample(candidates, size)))
            if not union_triangle_free(n, edges, M):
                continue
            slack = base.copy()
            for u, v in M:
                slack -= bits[u] ^ bits[v]
            if int(slack.min()) < 0:
                continue
            roots = valid_stub_pairs(n, slack)
            for w in range(n):
                for x in range(n):
                    if not roots[w][x]:
                        continue
                    d = dist[w][x]
                    s = n - 1 - d
                    if not (
                        d >= 3
                        and s >= 5
                        and d <= 2 * s
                        and 2 * s * p_of_d(d) < (d + 1) ** 2
                    ):
                        continue
                    path = geodesic_avoiding_bridges(n, edges, dist, w, x)
                    if path is None:
                        continue
                    Ds = tuple(sorted(dist[u][v] for u, v in M))
                    key = (d, s, Ds)
                    if key not in found:
                        found[key] = (tuple(edges), M, w, x, path)
                        dual_value, dual_weights = weighted_cut_dual_optimum(
                            n, edges, M, w, x, dist
                        )
                        print(
                            "FOUND",
                            key,
                            "gamma",
                            gamma_of(M, dist),
                            "budget",
                            rl_rhs(n, d),
                            "dual",
                            dual_value,
                            dual_weights,
                            "edges",
                            tuple(edges),
                            "M",
                            M,
                            "w,x,path",
                            (w, x, path),
                            flush=True,
                        )
        if trial and trial % 1000 == 0:
            print("progress", trial, "signatures", len(found), flush=True)
    print("DONE", len(found))


if __name__ == "__main__":
    search(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) if len(sys.argv) > 3 else 14)
