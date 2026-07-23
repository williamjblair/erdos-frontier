"""Exact exhaustive checks for the d=2s-1 canonical defect geometries.

This enumerates every mass-defect block order, every bipartite attachment
choice of the unique two-vertex component, and every overlap-defect interval
family for small ``s``.  It checks BFS alignment and the proposed
right-boundary cut family against every same-side pair at graph distance at
least four.  All operations use integer/Boolean graph arithmetic.
"""

from __future__ import annotations

from collections import deque
from itertools import product


def distances(n: int, edges: set[tuple[int, int]]) -> list[list[int]]:
    adjacency = [[] for _ in range(n)]
    for u, v in edges:
        adjacency[u].append(v)
        adjacency[v].append(u)
    answer = []
    for source in range(n):
        row = [-1] * n
        row[source] = 0
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if row[v] == -1:
                    row[v] = row[u] + 1
                    queue.append(v)
        answer.append(row)
    return answer


def cut_size(edges: set[tuple[int, int]], shore: set[int]) -> int:
    return sum((u in shore) != (v in shore) for u, v in edges)


def connected_without_edge(
    n: int, edges: set[tuple[int, int]], removed: tuple[int, int]
) -> bool:
    remaining = set(edges)
    remaining.remove(tuple(sorted(removed)))
    adjacency = [[] for _ in range(n)]
    for u, v in remaining:
        adjacency[u].append(v)
        adjacency[v].append(u)
    seen = {0}
    stack = [0]
    while stack:
        u = stack.pop()
        for v in adjacency[u]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return len(seen) == n


def canonical_shore(
    d: int,
    components: list[tuple[set[int], tuple[int, ...]]],
    coordinate: int,
) -> set[int]:
    shore = set(range(coordinate + 1))
    for vertices, attachments in components:
        if min(attachments) <= coordinate:
            shore.update(vertices)
    return shore


def eligible_pairs(dist: list[list[int]], colors: list[int]):
    n = len(dist)
    return [
        (u, v)
        for u in range(n)
        for v in range(u + 1, n)
        if colors[u] == colors[v] and dist[u][v] >= 4
    ]


def audit_cut_family(
    label: str,
    d: int,
    edges: set[tuple[int, int]],
    components: list[tuple[set[int], tuple[int, ...]]],
    cuts: list[int],
    colors: list[int],
) -> dict[str, object] | None:
    n = len(colors)
    dist = distances(n, edges)
    assert n == 3 * ((d + 1) // 2)
    assert dist[0][d] == d
    assert all(colors[u] != colors[v] for u, v in edges)
    assert all(connected_without_edge(n, edges, (i, i + 1)) for i in range(d))
    assert len(cuts) == (d + 1) // 2 - 1
    shores = [canonical_shore(d, components, coordinate) for coordinate in cuts]
    for coordinate, shore in zip(cuts, shores):
        if 0 not in shore or d in shore:
            return {"failure": "terminal", "label": label, "cut": coordinate}
        if cut_size(edges, shore) > 2:
            return {
                "failure": "capacity",
                "label": label,
                "cut": coordinate,
                "capacity": cut_size(edges, shore),
            }
    pairs = eligible_pairs(dist, colors)
    for u, v in pairs:
        crossed = sum((u in shore) != (v in shore) for shore in shores)
        if dist[u][v] > 2 * crossed + 2:
            return {
                "failure": "metric",
                "label": label,
                "pair": (u, v),
                "distance": dist[u][v],
                "crossed": crossed,
                "levels": (dist[0][u], dist[0][v]),
                "cuts": cuts,
                "edges": tuple(sorted(edges)),
                "components": components,
            }
    unaligned = [
        (u, v, dist[u][v], abs(dist[0][u] - dist[0][v]))
        for u, v in pairs
        if dist[u][v] != abs(dist[0][u] - dist[0][v])
    ]
    return {"unaligned": unaligned, "eligible_count": len(pairs)}


def mass_fixture(s: int, long_position: int, extra: tuple[int, int]):
    d = 2 * s - 1
    edges = {(i, i + 1) for i in range(d)}
    colors = [i % 2 for i in range(d + 1)]
    components: list[tuple[set[int], tuple[int, ...]]] = []
    cuts: list[int] = []
    cursor = 0
    next_vertex = d + 1
    for block in range(s - 1):
        if block == long_position:
            a, b = next_vertex, next_vertex + 1
            next_vertex += 2
            colors.extend([1 - cursor % 2, cursor % 2])
            attachments_a = [cursor, cursor + 2] if extra[0] else [cursor]
            attachments_b = [cursor + 1, cursor + 3] if extra[1] else [cursor + 3]
            edges.add(tuple(sorted((a, b))))
            for index in attachments_a:
                edges.add(tuple(sorted((a, index))))
            for index in attachments_b:
                edges.add(tuple(sorted((b, index))))
            attachments = tuple(sorted(attachments_a + attachments_b))
            components.append(({a, b}, attachments))
            cursor += 3
        else:
            vertex = next_vertex
            next_vertex += 1
            colors.append(1 - cursor % 2)
            edges.add(tuple(sorted((vertex, cursor))))
            edges.add(tuple(sorted((vertex, cursor + 2))))
            components.append(({vertex}, (cursor, cursor + 2)))
            cursor += 2
        cuts.append(cursor - 1)
    assert cursor == d and next_vertex == 3 * s
    return d, edges, components, cuts, colors


def overlap_start_families(s: int):
    """All length-two covers of ``range(2*s-1)`` with overlap defect one.

    The interval covering coordinate zero must start at zero.  Until the
    unique double-covered coordinate, subsequent starts advance by two; at
    that coordinate they advance by one; afterwards they again advance by
    two.  Thus the switch position ``1 <= switch < s`` determines the family
    uniquely.  This is the constructive normal form proved abstractly by
    ``overlapIntervalProfile`` and avoids an exponential combinations scan.
    """
    d = 2 * s - 1
    for switch in range(1, s):
        starts = tuple(range(0, 2 * switch, 2)) + tuple(
            range(2 * switch - 1, d - 1, 2)
        )
        assert len(starts) == s and len(set(starts)) == s
        covered = set()
        multiplicity = 0
        for start in starts:
            interval = {start, start + 1}
            covered.update(interval)
            multiplicity += len(interval)
        assert covered == set(range(d)) and multiplicity - len(covered) == 1
        yield starts


def overlap_fixture(s: int, starts: tuple[int, ...]):
    d = 2 * s - 1
    edges = {(i, i + 1) for i in range(d)}
    colors = [i % 2 for i in range(d + 1)]
    components: list[tuple[set[int], tuple[int, ...]]] = []
    cuts = []
    for offset, start in enumerate(starts):
        vertex = d + 1 + offset
        colors.append(1 - start % 2)
        edges.add(tuple(sorted((vertex, start))))
        edges.add(tuple(sorted((vertex, start + 2))))
        components.append(({vertex}, (start, start + 2)))
        cuts.append(start + 1)
    capacities = [
        cut_size(edges, canonical_shore(d, components, coordinate))
        for coordinate in cuts
    ]
    return d, edges, components, cuts, colors, capacities


def main() -> None:
    counts = {"mass": 0, "overlap": 0, "eligible": 0}
    first_unaligned: dict[str, object] | None = None
    for s in range(2, 17):
        for long_position, extra in product(range(s - 1), product((0, 1), repeat=2)):
            d, edges, components, cuts, colors = mass_fixture(s, long_position, extra)
            result = audit_cut_family(
                f"mass(s={s},long={long_position},extra={extra})",
                d,
                edges,
                components,
                cuts,
                colors,
            )
            counts["mass"] += 1
            assert result is not None
            counts["eligible"] += result["eligible_count"]
            if "failure" in result:
                print("COUNTEREXAMPLE", result)
                return
            if result["unaligned"] and first_unaligned is None:
                first_unaligned = {"label": f"mass(s={s},long={long_position},extra={extra})", "pairs": result["unaligned"]}

        overlap_count = 0
        for starts in overlap_start_families(s):
            overlap_count += 1
            d, edges, components, cuts, colors, capacities = overlap_fixture(s, starts)
            bad = [index for index, capacity in enumerate(capacities) if capacity > 2]
            assert len(bad) == 1 and capacities[bad[0]] == 3, (s, starts, capacities)
            selected = [coordinate for index, coordinate in enumerate(cuts) if index != bad[0]]
            result = audit_cut_family(
                f"overlap(s={s},starts={starts},omit={cuts[bad[0]]})",
                d,
                edges,
                components,
                selected,
                colors,
            )
            counts["overlap"] += 1
            assert result is not None
            counts["eligible"] += result["eligible_count"]
            if "failure" in result:
                print("COUNTEREXAMPLE", result)
                return
            if result["unaligned"] and first_unaligned is None:
                first_unaligned = {"label": f"overlap(s={s},starts={starts})", "pairs": result["unaligned"]}
        assert overlap_count == s - 1, (s, overlap_count)

    print("PASS", counts)
    print("first_unaligned", first_unaligned)


if __name__ == "__main__":
    main()
