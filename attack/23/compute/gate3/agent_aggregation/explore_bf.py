"""Exact small-instance exploration for the BF-RL aggregation subtask.

This is discovery-only.  It enumerates connected bipartite supply graphs,
valid demand sets, and rooted stub pairs, retaining a root--stub geodesic
whose every edge is a nonbridge.  Candidate scalar inequalities can then be
falsified on the resulting exact records.
"""

from __future__ import annotations

from collections import defaultdict
from itertools import combinations

import numpy as np

from compute23.gate2.common import adj_masks, parse_graph6
from compute23.gate3.rl_lib import (
    all_dists,
    gamma_of,
    gen_bipartite,
    geodesics_between,
    m_candidates,
    p_of_d,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


def connected_without_edge(n: int, edges: list[tuple[int, int]], edge: tuple[int, int]) -> bool:
    kept = [e for e in edges if e != edge and e != edge[::-1]]
    adj = adj_masks(n, kept)
    seen = 1
    frontier = 1
    while frontier:
        x = (frontier & -frontier).bit_length() - 1
        frontier &= frontier - 1
        new = adj[x] & ~seen
        seen |= new
        frontier |= new
    return seen.bit_count() == n


def has_all_nonbridge_geodesic(n, edges, dist, w, x0) -> bool:
    adj = adj_masks(n, edges)
    nonbridges = {
        tuple(sorted(e))
        for e in edges
        if connected_without_edge(n, edges, tuple(sorted(e)))
    }
    return any(
        all(tuple(sorted((path[i], path[i + 1]))) in nonbridges for i in range(len(path) - 1))
        for path in geodesics_between(n, adj, dist, w, x0)
    )


def m_subsets(candidates, mmax):
    for k in range(2, min(mmax, len(candidates)) + 1):
        yield from combinations(candidates, k)


def enumerate_bf(nmax: int = 9, mmax: int = 3):
    records = {}
    for n in range(5, nmax + 1):
        bit = xor_bits(n)
        graph_count = rooted_count = 0
        for line in gen_bipartite(n):
            nn, edges = parse_graph6(line)
            assert nn == n
            edges = [tuple(sorted(e)) for e in edges]
            dist = all_dists(n, edges)
            candidates = m_candidates(n, dist)
            if len(candidates) < 2:
                continue
            graph_count += 1
            supply = np.zeros(1 << n, dtype=np.int32)
            for a, b in edges:
                supply += bit[a] ^ bit[b]
            crossing = {e: bit[e[0]] ^ bit[e[1]] for e in candidates}
            for M in m_subsets(candidates, mmax):
                if not union_triangle_free(n, edges, M):
                    continue
                slack = supply.copy()
                for e in M:
                    slack -= crossing[e]
                if slack.min() < 0:
                    continue
                roots = valid_stub_pairs(n, slack)
                Ds = tuple(sorted((dist[a][b] for a, b in M), reverse=True))
                gam = gamma_of(M, dist)
                for w in range(n):
                    for x0 in range(n):
                        if not roots[w][x0] or not has_all_nonbridge_geodesic(n, edges, dist, w, x0):
                            continue
                        d = dist[w][x0]
                        s = n - 1 - d
                        rooted_count += 1
                        key = (n, d, s, Ds, gam)
                        records.setdefault(key, (line, tuple(edges), M, w, x0))
        print(f"n={n} candidate_graphs={graph_count} bf_rootings={rooted_count} records={len(records)}")
    return records


def report(records):
    by_ds = defaultdict(list)
    kills = defaultdict(list)
    for key, witness in records.items():
        n, d, s, Ds, gam = key
        by_ds[d, s].append((gam, Ds, witness))
        m = len(Ds)
        excess = sum(D - 4 for D in Ds)
        candidates = {
            "raw_excess_2s-4": excess <= 2 * s - 4,
            "sumD_2s+4m-4": sum(Ds) <= 2 * s + 4 * m - 4,
            "square_excess": sum((D + 1) ** 2 - 25 for D in Ds) <= (2 * s + 1) ** 2 - 25,
            "m_le_s": m <= s,
            "m_le_s2_over4": 4 * m <= s * s,
        }
        for name, ok in candidates.items():
            if not ok and len(kills[name]) < 5:
                kills[name].append((key, witness))
    for ds in sorted(by_ds):
        top = sorted(by_ds[ds], reverse=True)[:5]
        print("DS", ds, [(gam, Ds) for gam, Ds, _ in top])
    for name, examples in kills.items():
        print("KILLS", name, [(key, wit[0]) for key, wit in examples])


if __name__ == "__main__":
    report(enumerate_bf())
