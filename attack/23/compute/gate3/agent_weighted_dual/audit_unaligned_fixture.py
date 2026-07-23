"""Exact audit of a binary-layer BF-RL instance with an unaligned demand.

This script uses only integer graph operations and enumerates all 2^14 cuts.
It is a falsification fixture for the tempting claim that a bridge-free
root--stub geodesic forces every internal demand to be level-aligned.
"""

from __future__ import annotations

from collections import deque


N = 14
W = 0
X0 = 7
B = (
    (0, 1),
    (0, 8),
    (1, 2),
    (1, 9),
    (2, 3),
    (2, 8),
    (2, 10),
    (3, 4),
    (3, 9),
    (4, 5),
    (4, 10),
    (4, 12),
    (5, 6),
    (5, 11),
    (5, 13),
    (6, 7),
    (6, 12),
    (7, 13),
    (8, 9),
    (10, 11),
    (12, 13),
)
M = ((9, 11), (7, 10))
CORRIDOR = tuple(range(8))


def adjacency(edges: tuple[tuple[int, int], ...]) -> list[list[int]]:
    adj = [[] for _ in range(N)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def bfs(source: int, edges: tuple[tuple[int, int], ...]) -> list[int]:
    adj = adjacency(edges)
    dist = [-1] * N
    dist[source] = 0
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if dist[v] == -1:
                dist[v] = dist[u] + 1
                queue.append(v)
    return dist


def connected_after_deleting(edge: tuple[int, int]) -> bool:
    remaining = tuple(e for e in B if e != edge)
    return all(distance >= 0 for distance in bfs(W, remaining))


def crosses(mask: int, edge: tuple[int, int]) -> bool:
    u, v = edge
    return ((mask >> u) & 1) != ((mask >> v) & 1)


def rfc_min_slack() -> tuple[int, int]:
    minimum = len(B)
    witness = 0
    for mask in range(1 << N):
        if (mask >> W) & 1:
            continue
        supply = sum(crosses(mask, edge) for edge in B)
        demand = sum(crosses(mask, edge) for edge in M)
        rooted = (mask >> X0) & 1
        slack = supply - demand - rooted
        if slack < minimum:
            minimum = slack
            witness = mask
    return minimum, witness


def triangle_free(edges: tuple[tuple[int, int], ...]) -> bool:
    adj = adjacency(edges)
    for u in range(N):
        neighbors = set(adj[u])
        for v in neighbors:
            if any(z in neighbors for z in adj[v]):
                return False
    return True


def main() -> None:
    assert len(set(B)) == len(B)
    assert len(set(M)) == len(M)
    assert not (set(B) & set(M))
    assert all(u < v for u, v in B + M)

    levels = bfs(W, B)
    assert levels == [0, 1, 2, 3, 4, 5, 6, 7, 1, 2, 3, 4, 5, 6]
    assert all(level >= 0 for level in levels)
    assert all(abs(levels[u] - levels[v]) == 1 for u, v in B)
    assert max(levels.count(level) for level in range(8)) == 2

    all_distances = [bfs(source, B) for source in range(N)]
    assert all_distances[W][X0] == 7
    assert all(all_distances[u][v] == 4 for u, v in M)
    assert abs(levels[9] - levels[11]) == 2
    assert all_distances[9][11] - abs(levels[9] - levels[11]) == 2
    assert abs(levels[7] - levels[10]) == 4

    assert all(connected_after_deleting((u, v)) for u, v in zip(CORRIDOR, CORRIDOR[1:]))
    assert triangle_free(B + M)

    minimum, witness = rfc_min_slack()
    assert minimum == 0, (minimum, witness)

    d = all_distances[W][X0]
    s = N - 1 - d
    p = 1  # d = 7 is odd and at least five.
    gamma = sum((all_distances[u][v] + 1) ** 2 for u, v in M)
    budget = s * (2 * d + 2 + s) + 2 * s * p
    assert (N, d, s, gamma, budget) == (14, 7, 6, 50, 144)
    assert s >= 5 and d <= 2 * s and 2 * s * p < (d + 1) ** 2

    print("levels", levels)
    print("demand_data", tuple((edge, all_distances[edge[0]][edge[1]], abs(levels[edge[0]] - levels[edge[1]])) for edge in M))
    print("corridor_edges_nonbridges", True)
    print("triangle_free", True)
    print("RFC_min_slack", minimum, "witness_mask", witness)
    print("n,d,s,gamma,budget", N, d, s, gamma, budget)


if __name__ == "__main__":
    main()
