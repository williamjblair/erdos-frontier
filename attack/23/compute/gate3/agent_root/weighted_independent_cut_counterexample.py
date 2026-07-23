#!/usr/bin/env python3
"""Exact counterexample to the weighted-independent-set shortcut for #23."""

from itertools import combinations


N = 8
EDGES = (
    (0, 3), (0, 4), (1, 4), (0, 5),
    (1, 5), (2, 5), (1, 6), (2, 6),
    (3, 6), (2, 7), (3, 7), (4, 7),
)


def crossing(mask: int, edge: tuple[int, int]) -> bool:
    u, v = edge
    return bool((mask >> u) & 1) != bool((mask >> v) & 1)


def certificate() -> dict[str, object]:
    adjacency = [set() for _ in range(N)]
    for u, v in EDGES:
        adjacency[u].add(v)
        adjacency[v].add(u)
    assert all(len(neighbours) == 3 for neighbours in adjacency)
    assert all(
        not ({v, w} <= adjacency[u]) or w not in adjacency[v]
        for u in range(N)
        for v, w in combinations(range(N), 2)
    )
    best_independent_weight = -1
    best_independent_mask = 0
    best_cut = -1
    best_cut_mask = 0
    for mask in range(1 << N):
        if not any(
            ((mask >> u) & 1) and ((mask >> v) & 1)
            for u, v in EDGES
        ):
            weight = sum(
                len(adjacency[v]) for v in range(N) if (mask >> v) & 1
            )
            if weight > best_independent_weight:
                best_independent_weight = weight
                best_independent_mask = mask
        cut = sum(crossing(mask, edge) for edge in EDGES)
        if cut > best_cut:
            best_cut = cut
            best_cut_mask = mask
    edge_count = len(EDGES)
    beta = edge_count - best_cut
    return {
        "n": N,
        "edge_count": edge_count,
        "degrees": tuple(len(neighbours) for neighbours in adjacency),
        "maximum_independent_degree_sum": best_independent_weight,
        "independent_mask": best_independent_mask,
        "weighted_claim_scaled_lhs": 25 * best_independent_weight,
        "weighted_claim_scaled_rhs": 25 * edge_count - N * N,
        "maximum_cut": best_cut,
        "cut_mask": best_cut_mask,
        "beta": beta,
        "erdos23_scaled_lhs": 25 * beta,
        "erdos23_scaled_rhs": N * N,
    }


if __name__ == "__main__":
    result = certificate()
    assert result["weighted_claim_scaled_lhs"] < result["weighted_claim_scaled_rhs"]
    assert result["erdos23_scaled_lhs"] <= result["erdos23_scaled_rhs"]
    print(result)
