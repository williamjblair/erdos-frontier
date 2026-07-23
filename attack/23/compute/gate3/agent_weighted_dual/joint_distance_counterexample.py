#!/usr/bin/env python3
"""Exact counterexample to the proposed two-demand joint distance bound.

This does **not** contradict RL.  It kills only the sufficient intermediate

    D1 + D2 <= n + p(d) - 2.

The construction starts from an exhaustively verified 11-vertex rooted
instance.  It composes two elementary cut gadgets:

* a chain of C4 diamonds moves the common endpoint of both demands; and
* an even cycle moves the root while leaving an all-nonbridge root geodesic.

The local inequalities used in the composition are checked by complete
truth tables.  Thus the 76-vertex RFC verification is a symbolic exact-cut
proof, not a random or floating-point test and not an infeasible 2^76 scan.
"""

from __future__ import annotations

from collections import deque
from itertools import product


Edge = tuple[int, int]


BASE_N = 11
BASE_EDGES: tuple[Edge, ...] = (
    (0, 7),
    (1, 7),
    (2, 7),
    (0, 8),
    (1, 8),
    (2, 8),
    (3, 9),
    (4, 9),
    (5, 9),
    (6, 9),
    (0, 10),
    (1, 10),
    (3, 10),
    (4, 10),
)
BASE_DEMANDS: tuple[Edge, ...] = ((2, 5), (2, 6))
BASE_ROOT = 0
BASE_STUB = 1


def bit(mask: int, vertex: int) -> int:
    return (mask >> vertex) & 1


def sep(left: int, right: int) -> int:
    return left ^ right


def cut_count(edges: tuple[Edge, ...] | list[Edge], mask: int) -> int:
    return sum(bit(mask, u) ^ bit(mask, v) for u, v in edges)


def exact_base_rfc() -> int:
    """Check symmetric RFC on all 2^11 cuts and return its minimum slack."""

    minimum = 10**9
    for mask in range(1 << BASE_N):
        supply = cut_count(BASE_EDGES, mask)
        demand = cut_count(BASE_DEMANDS, mask)
        rooted = sep(bit(mask, BASE_ROOT), bit(mask, BASE_STUB))
        slack = supply - demand - rooted
        assert slack >= 0, mask
        minimum = min(minimum, slack)
    return minimum


def exact_local_truth_tables() -> dict[str, int]:
    """Check the two cut inequalities used by gadget composition."""

    endpoint_rows = root_rows = diamond_rows = 0

    # Moving the common endpoint z of two demands to z' changes their cut
    # load by at most two, and only when z,z' are separated.
    for z, zp, a, b in product((0, 1), repeat=4):
        old = sep(z, a) + sep(z, b)
        new = sep(zp, a) + sep(zp, b)
        assert new <= old + 2 * sep(z, zp)
        endpoint_rows += 1

    # Moving the root r to w costs at most the separation of w,r.
    for w, r, x in product((0, 1), repeat=3):
        assert sep(w, x) <= sep(r, x) + sep(w, r)
        root_rows += 1

    # A C4 diamond consists of two internally disjoint length-two paths.
    # Every cut separating its endpoints crosses at least two supply edges.
    for z, zp, a, b in product((0, 1), repeat=4):
        crossing = sep(z, a) + sep(a, zp) + sep(z, b) + sep(b, zp)
        assert 2 * sep(z, zp) <= crossing
        diamond_rows += 1

    return {
        "endpoint_move": endpoint_rows,
        "root_move": root_rows,
        "diamond": diamond_rows,
    }


def add_diamond_chain(
    edges: list[Edge], start: int, blocks: int, next_vertex: int
) -> tuple[int, int]:
    endpoint = start
    for _ in range(blocks):
        upper, lower, new_endpoint = next_vertex, next_vertex + 1, next_vertex + 2
        next_vertex += 3
        edges.extend(
            (
                (endpoint, upper),
                (upper, new_endpoint),
                (endpoint, lower),
                (lower, new_endpoint),
            )
        )
        endpoint = new_endpoint
    return endpoint, next_vertex


def add_antipodal_even_cycle(
    edges: list[Edge], old_root: int, half_length: int, next_vertex: int
) -> tuple[int, int, tuple[int, ...]]:
    first_internal = tuple(range(next_vertex, next_vertex + half_length - 1))
    next_vertex += half_length - 1
    second_internal = tuple(range(next_vertex, next_vertex + half_length - 1))
    next_vertex += half_length - 1
    new_root = next_vertex
    next_vertex += 1

    first_path = (old_root,) + first_internal + (new_root,)
    second_path = (old_root,) + second_internal + (new_root,)
    edges.extend(zip(first_path, first_path[1:]))
    edges.extend(zip(second_path, second_path[1:]))
    # Return the root-to-old-root orientation used by the displayed geodesic.
    return new_root, next_vertex, tuple(reversed(first_path))


def adjacency(n: int, edges: tuple[Edge, ...]) -> list[list[int]]:
    out = [[] for _ in range(n)]
    for u, v in edges:
        out[u].append(v)
        out[v].append(u)
    return out


def distances_from(n: int, edges: tuple[Edge, ...], source: int) -> list[int]:
    adj = adjacency(n, edges)
    distance = [-1] * n
    distance[source] = 0
    queue = deque((source,))
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if distance[v] < 0:
                distance[v] = distance[u] + 1
                queue.append(v)
    assert all(value >= 0 for value in distance)
    return distance


def is_bridge(n: int, edges: tuple[Edge, ...], edge: Edge) -> bool:
    target = tuple(sorted(edge))
    kept = tuple(e for e in edges if tuple(sorted(e)) != target)
    return any(value < 0 for value in distances_allow_disconnected(n, kept, edge[0]))


def distances_allow_disconnected(
    n: int, edges: tuple[Edge, ...], source: int
) -> list[int]:
    adj = adjacency(n, edges)
    distance = [-1] * n
    distance[source] = 0
    queue = deque((source,))
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if distance[v] < 0:
                distance[v] = distance[u] + 1
                queue.append(v)
    return distance


def bipartition(n: int, edges: tuple[Edge, ...]) -> tuple[int, ...]:
    adj = adjacency(n, edges)
    colour = [-1] * n
    colour[0] = 0
    queue = deque((0,))
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if colour[v] < 0:
                colour[v] = 1 - colour[u]
                queue.append(v)
            else:
                assert colour[v] != colour[u]
    assert all(value >= 0 for value in colour)
    return tuple(colour)


def partner_distance(d: int) -> int:
    if d == 1:
        return 3
    if d % 2 == 0:
        return 2
    return 1


def build_counterexample(
    diamond_blocks: int = 16, root_half_cycle: int = 9
) -> dict[str, object]:
    edges = list(BASE_EDGES)
    common_endpoint, next_vertex = add_diamond_chain(
        edges, BASE_DEMANDS[0][0], diamond_blocks, BASE_N
    )
    new_root, n, root_to_old = add_antipodal_even_cycle(
        edges, BASE_ROOT, root_half_cycle, next_vertex
    )
    edges_tuple = tuple(tuple(sorted(edge)) for edge in edges)
    assert len(edges_tuple) == len(set(edges_tuple))
    demands = ((common_endpoint, 5), (common_endpoint, 6))

    colour = bipartition(n, edges_tuple)
    assert all(colour[u] == colour[v] for u, v in demands)
    distance_root = distances_from(n, edges_tuple, new_root)
    d = distance_root[BASE_STUB]
    demand_distances = tuple(
        distances_from(n, edges_tuple, u)[v] for u, v in demands
    )
    assert min(demand_distances) >= 4

    # No B-M-B triangle because each demand has B-distance > 2.  The only
    # possible two-demand triangle would additionally need the B-edge 5--6.
    assert min(demand_distances) > 2
    assert (5, 6) not in edges_tuple

    root_geodesic = root_to_old + (7, BASE_STUB)
    assert len(root_geodesic) - 1 == d
    assert all(
        tuple(sorted(edge)) in edges_tuple
        for edge in zip(root_geodesic, root_geodesic[1:])
    )
    bridge_flags = tuple(
        is_bridge(n, edges_tuple, edge)
        for edge in zip(root_geodesic, root_geodesic[1:])
    )
    assert not any(bridge_flags)

    p = partner_distance(d)
    s = n - 1 - d
    distance_sum = sum(demand_distances)
    joint_rhs = n + p - 2
    strict_left = 2 * s * p
    strict_right = (d + 1) ** 2
    total_cost = sum((value + 1) ** 2 for value in demand_distances)
    rl_budget = s * (2 * d + 2 + s) + 2 * s * p

    assert n >= 14
    assert 5 <= s
    assert d <= 2 * s - 2
    assert strict_left < strict_right
    assert distance_sum > joint_rhs
    assert total_cost <= rl_budget  # The counterexample is not an RL failure.

    return {
        "n": n,
        "edge_count": len(edges_tuple),
        "diamond_blocks": diamond_blocks,
        "root_half_cycle": root_half_cycle,
        "root": new_root,
        "stub": BASE_STUB,
        "d": d,
        "s": s,
        "p": p,
        "demands": demands,
        "demand_distances": demand_distances,
        "distance_sum": distance_sum,
        "joint_rhs": joint_rhs,
        "joint_excess": distance_sum - joint_rhs,
        "strict_pair": (strict_left, strict_right),
        "root_geodesic": root_geodesic,
        "root_geodesic_bridge_flags": bridge_flags,
        "total_cost": total_cost,
        "rl_budget": rl_budget,
        "edges": edges_tuple,
    }


def main() -> None:
    print("base_rfc_min_slack", exact_base_rfc())
    print("local_truth_tables", exact_local_truth_tables())
    print("counterexample", build_counterexample())


if __name__ == "__main__":
    main()
