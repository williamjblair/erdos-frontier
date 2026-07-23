"""Exact regression fixtures for the revised component-ledger proof of G-A."""

from __future__ import annotations

from collections import deque
from itertools import combinations


VERTICES = tuple(range(7))
EDGES = {
    frozenset(edge)
    for edge in ((0, 1), (1, 2), (2, 3), (0, 4), (2, 4), (1, 5), (5, 6))
}
STUB_PAIR = (0, 3)
M_PAIR = (4, 6)
P = (0, 1, 2, 3)
Q = (4, 0, 1, 5, 6)


def adjacent(vertex: int) -> set[int]:
    return {
        next(iter(edge - {vertex}))
        for edge in EDGES
        if vertex in edge
    }


def distance(source: int, target: int) -> int:
    queue = deque([(source, 0)])
    seen = {source}
    while queue:
        vertex, depth = queue.popleft()
        if vertex == target:
            return depth
        for neighbor in adjacent(vertex) - seen:
            seen.add(neighbor)
            queue.append((neighbor, depth + 1))
    raise AssertionError("fixture graph is disconnected")


def separates(subset: set[int], pair: tuple[int, int]) -> bool:
    return (pair[0] in subset) != (pair[1] in subset)


def cut_size(subset: set[int]) -> int:
    return sum(len(edge & subset) == 1 for edge in EDGES)


def path_length(path: tuple[int, ...]) -> int:
    assert all(frozenset((left, right)) in EDGES for left, right in zip(path, path[1:]))
    return len(path) - 1


def test_hostile_audit_fixture_satisfies_the_exact_two_demand_condition() -> None:
    left = {0, 2, 5}
    right = set(VERTICES) - left
    assert all(
        len(edge & left) == 1 and len(edge & right) == 1
        for edge in EDGES
    )
    assert frozenset(M_PAIR) not in EDGES
    union_edges = EDGES | {frozenset(M_PAIR)}
    assert not any(
        all(frozenset(edge) in union_edges for edge in ((a, b), (a, c), (b, c)))
        for a, b, c in combinations(VERTICES, 3)
    )

    for size in range(len(VERTICES) + 1):
        for values in combinations(VERTICES, size):
            subset = set(values)
            demand = int(separates(subset, STUB_PAIR)) + int(separates(subset, M_PAIR))
            assert demand <= cut_size(subset)

    assert path_length(P) == distance(*STUB_PAIR) == 3
    assert path_length(Q) == distance(*M_PAIR) == 4


def test_old_exceptional_subclaim_fails_but_repaired_bound_is_tight() -> None:
    # Delete P.  The exceptional initial-tail component C={4} has unused
    # attachments at corridor positions 0 and 2.
    component = {4}
    attachments = {
        index
        for index, vertex in enumerate(P)
        if any(frozenset((vertex, member)) in EDGES for member in component)
    }
    assert attachments == {0, 2}

    ridden_edges = {
        frozenset((left, right))
        for left, right in zip(P, P[1:])
    } & {
        frozenset((left, right))
        for left, right in zip(Q, Q[1:])
    }
    assert ridden_edges == {frozenset((0, 1))}

    first_visit = 0
    last_visit = 1
    interval_ridden = {
        frozenset((P[index], P[index + 1]))
        for index in range(min(attachments), max(attachments))
    } & ridden_edges
    q_component = len(component & set(Q))

    # This is the exact sentence rejected by the first hostile audit.
    assert max(attachments) > first_visit
    assert interval_ridden

    # The repaired exceptional-component estimate is valid and tight.
    assert len(interval_ridden) == q_component == 1
    assert min(last_visit, max(attachments)) - first_visit <= q_component


def test_fixture_obeys_both_symmetric_single_edge_bounds() -> None:
    n = len(VERTICES)
    d = distance(*STUB_PAIR)
    D = distance(*M_PAIR)
    slack = n - 1 - d
    assert D <= 2 * slack
    assert 2 * D <= 2 * slack + d
