#!/usr/bin/env python3
"""Exact small-corpus record for a false three-demand pair bound.

The rooted ``n=76`` diamond-chain counterexample can be completed by the
parity-minimal partner path, and therefore also kills the proposed unrooted
three-demand estimate.  This order-nine scan is retained only to document
the misleading finite evidence; it is not a live conjecture.
"""

from __future__ import annotations

import argparse
from itertools import combinations

import numpy as np

from compute23.gate2.common import parse_graph6
from compute23.gate3.rl_lib import (
    all_dists,
    gen_bipartite,
    m_candidates,
    union_triangle_free,
    xor_bits,
)


def run(nmax: int) -> dict[str, object]:
    valid = failures = 0
    equality = 0
    first = None
    for n in range(5, nmax + 1):
        bits = xor_bits(n)
        for graph6 in gen_bipartite(n):
            nn, b_edges = parse_graph6(graph6)
            assert nn == n
            distances = all_dists(n, b_edges)
            candidates = m_candidates(n, distances)
            if len(candidates) < 3:
                continue
            supply = np.zeros(1 << n, dtype=np.int16)
            for u, v in b_edges:
                supply += bits[u] ^ bits[v]
            demand_cuts = {
                edge: bits[edge[0]] ^ bits[edge[1]] for edge in candidates
            }
            for demands in combinations(candidates, 3):
                if not union_triangle_free(n, b_edges, demands):
                    continue
                slack = supply.copy()
                for edge in demands:
                    slack -= demand_cuts[edge]
                if int(slack.min()) < 0:
                    continue
                valid += 1
                demand_distances = tuple(distances[u][v] for u, v in demands)
                top_two = sum(sorted(demand_distances, reverse=True)[:2])
                if top_two == n - 2:
                    equality += 1
                if top_two > n - 2:
                    failures += 1
                    if first is None:
                        first = (graph6, demands, demand_distances, top_two, n - 2)
    return {
        "nmax": nmax,
        "valid": valid,
        "equality": equality,
        "failures": failures,
        "first": first,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--nmax", type=int, default=9)
    args = parser.parse_args()
    print(run(args.nmax))


if __name__ == "__main__":
    main()
