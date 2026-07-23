"""Exact exhaustive multiset-gate audit on every rooted |M|=2 instance n<=9."""

from __future__ import annotations

from itertools import combinations

import numpy as np

from compute23.gate2.common import parse_graph6
from compute23.gate3.rl_lib import (
    all_dists,
    gen_bipartite,
    m_candidates,
    rl_rhs,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)
from compute23.gate3.agent_aggregation.distance_multiset_completion import (
    multiset_completion_order,
)


def run_audit() -> dict[str, object]:
    rooted = gate_pass = gate_fail = rl_fail = 0
    first_gate_fail = None
    profiles = set()
    for n in range(5, 10):
        bit = xor_bits(n)
        for graph6 in gen_bipartite(n):
            nn, b_edges = parse_graph6(graph6)
            assert nn == n
            distances = all_dists(n, b_edges)
            candidates = m_candidates(n, distances)
            supply = np.zeros(1 << n, dtype=np.int32)
            for u, v in b_edges:
                supply += bit[u] ^ bit[v]
            edge_cuts = {edge: bit[edge[0]] ^ bit[edge[1]] for edge in candidates}
            for m_edges in combinations(candidates, 2):
                if not union_triangle_free(n, b_edges, m_edges):
                    continue
                slack = supply.copy()
                for edge in m_edges:
                    slack -= edge_cuts[edge]
                if int(slack.min()) < 0:
                    continue
                valid = valid_stub_pairs(n, slack)
                demand_distances = tuple(distances[u][v] for u, v in m_edges)
                order = multiset_completion_order(demand_distances)
                gamma = sum((distance + 1) ** 2 for distance in demand_distances)
                for root in range(n):
                    for stub in range(n):
                        if not valid[root][stub]:
                            continue
                        rooted += 1
                        d = distances[root][stub]
                        budget = rl_rhs(n, d)
                        if gamma > budget:
                            rl_fail += 1
                        if order**2 <= budget:
                            gate_pass += 1
                        else:
                            gate_fail += 1
                            profile = (
                                n,
                                d,
                                n - 1 - d,
                                tuple(sorted(demand_distances)),
                                gamma,
                                order,
                                budget,
                            )
                            profiles.add(profile)
                            if first_gate_fail is None:
                                first_gate_fail = {
                                    "graph6": graph6,
                                    "m_edges": m_edges,
                                    "root": root,
                                    "stub": stub,
                                    "profile": profile,
                                }
    return {
        "rooted": rooted,
        "gate_pass": gate_pass,
        "gate_fail": gate_fail,
        "rl_fail": rl_fail,
        "first_gate_fail": first_gate_fail,
        "failure_profiles": tuple(sorted(profiles)),
    }


if __name__ == "__main__":
    print(run_audit())
