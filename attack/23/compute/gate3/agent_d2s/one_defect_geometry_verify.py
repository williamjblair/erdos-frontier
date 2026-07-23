"""Exact bounded falsification check for the Erdős 23 one-defect row.

This script constructs every canonical ``d = 2s-1`` mass-defect and
overlap-defect supply graph for ``5 <= s <= 8``.  In the mass geometry it
also constructs all four bipartite-compatible optional-attachment patterns
inside the unique length-three block.

For each graph it checks, using only Python integers and finite sets:

* connectedness, bipartiteness, and the claimed root--stub geodesic length;
* the exact interval multiplicities of the advertised defect geometry;
* the proposed right-end cuts, including terminal separation and capacity;
* ``D <= 2r+2`` for every same-side vertex pair at supply distance at least
  four, where ``r`` is the number of selected cuts separating the pair;
* the BFS-level alignment used by the independent BinaryLayers route; and
* the RL budget for every subset of legal pairs satisfying all selected-cut
  capacity constraints.

The last check is an exact dynamic program over *all* such subsets.  They
form a superset of the RFC-valid internal-edge sets: RFC at a selected cut
with terminal load one and supply capacity at most two permits at most one
internal edge to cross it.  The script is falsification support only; it is
not a proof of the quantified graph lemmas formalized in Lean.
"""

from __future__ import annotations

from collections import deque
from dataclasses import asdict, dataclass
import json
from typing import Iterable


Edge = tuple[int, int]


@dataclass(frozen=True)
class Component:
    vertices: tuple[int, ...]
    attachments: tuple[int, ...]
    interval: tuple[int, int]


@dataclass(frozen=True)
class Geometry:
    kind: str
    s: int
    defect_position: int
    optional_mask: int
    d: int
    n: int
    edges: tuple[Edge, ...]
    components: tuple[Component, ...]
    selected_right_ends: tuple[int, ...]


@dataclass(frozen=True)
class GeometryCheck:
    legal_pairs: int
    cut_feasible_sets_at_least_two: int
    largest_cut_size: int
    least_pair_margin: int
    largest_set_cost: int
    set_budget_margin: int


@dataclass(frozen=True)
class AuditSummary:
    verdict: str
    s_values: tuple[int, ...]
    mass_cases: int
    overlap_cases: int
    geometry_cases: int
    legal_pairs: int
    cut_feasible_sets_at_least_two: int
    largest_cut_size: int
    least_pair_margin: int
    least_set_budget_margin: int


def _edge(a: int, b: int) -> Edge:
    assert a != b
    return (a, b) if a < b else (b, a)


def _normalise_edges(edges: Iterable[Edge]) -> tuple[Edge, ...]:
    normalised = tuple(sorted({_edge(a, b) for a, b in edges}))
    return normalised


def mass_geometry(s: int, defect_position: int, optional_mask: int) -> Geometry:
    """One length-three two-vertex block and ``s-2`` singleton blocks."""

    assert s >= 2
    assert 0 <= defect_position < s - 1
    assert 0 <= optional_mask < 4
    d = 2 * s - 1
    edges: list[Edge] = [(i, i + 1) for i in range(d)]
    components: list[Component] = []
    cursor = 0
    next_vertex = d + 1
    for block in range(s - 1):
        if block == defect_position:
            left, right = next_vertex, next_vertex + 1
            next_vertex += 2
            edges.extend(
                (
                    (left, right),
                    (left, cursor),
                    (right, cursor + 3),
                )
            )
            # Bipartiteness permits precisely these two additional edges.
            if optional_mask & 1:
                edges.append((right, cursor + 1))
            if optional_mask & 2:
                edges.append((left, cursor + 2))
            attachments = [cursor, cursor + 3]
            if optional_mask & 1:
                attachments.append(cursor + 1)
            if optional_mask & 2:
                attachments.append(cursor + 2)
            components.append(
                Component(
                    vertices=(left, right),
                    attachments=tuple(sorted(attachments)),
                    interval=(cursor, cursor + 3),
                )
            )
            cursor += 3
        else:
            vertex = next_vertex
            next_vertex += 1
            edges.extend(((vertex, cursor), (vertex, cursor + 2)))
            components.append(
                Component(
                    vertices=(vertex,),
                    attachments=(cursor, cursor + 2),
                    interval=(cursor, cursor + 2),
                )
            )
            cursor += 2
    assert cursor == d
    assert next_vertex == 3 * s
    return Geometry(
        kind="mass",
        s=s,
        defect_position=defect_position,
        optional_mask=optional_mask,
        d=d,
        n=3 * s,
        edges=_normalise_edges(edges),
        components=tuple(components),
        # There are exactly s-1 blocks.  Keeping the terminal right-end cut
        # is intentional and checks the terminal-truncation boundary.
        selected_right_ends=tuple(component.interval[1] for component in components),
    )


def overlap_geometry(s: int, defect_position: int) -> Geometry:
    """Length-two singleton blocks with one adjacent one-edge overlap."""

    assert s >= 2
    assert 0 <= defect_position < s - 1
    d = 2 * s - 1
    starts = [0]
    for transition in range(s - 1):
        step = 1 if transition == defect_position else 2
        starts.append(starts[-1] + step)
    assert starts[-1] + 2 == d
    edges: list[Edge] = [(i, i + 1) for i in range(d)]
    components: list[Component] = []
    next_vertex = d + 1
    for start in starts:
        vertex = next_vertex
        next_vertex += 1
        edges.extend(((vertex, start), (vertex, start + 2)))
        components.append(
            Component(
                vertices=(vertex,),
                attachments=(start, start + 2),
                interval=(start, start + 2),
            )
        )
    assert next_vertex == 3 * s
    # The left block at the overlap has a capacity-three right-end cut: the
    # corridor edge, its own closing attachment, and the next block's closing
    # attachment.  Omitting exactly that end leaves s-1 capacity-two cuts.
    selected = tuple(
        component.interval[1]
        for block, component in enumerate(components)
        if block != defect_position
    )
    assert len(selected) == s - 1
    return Geometry(
        kind="overlap",
        s=s,
        defect_position=defect_position,
        optional_mask=0,
        d=d,
        n=3 * s,
        edges=_normalise_edges(edges),
        components=tuple(components),
        selected_right_ends=selected,
    )


def all_geometries(s_values: Iterable[int] = range(5, 9)) -> Iterable[Geometry]:
    for s in s_values:
        for position in range(s - 1):
            for optional_mask in range(4):
                yield mass_geometry(s, position, optional_mask)
        for position in range(s - 1):
            yield overlap_geometry(s, position)


def _adjacency(geometry: Geometry) -> tuple[frozenset[int], ...]:
    adjacency = [set() for _ in range(geometry.n)]
    for a, b in geometry.edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    return tuple(frozenset(neighbours) for neighbours in adjacency)


def _all_distances(geometry: Geometry) -> tuple[tuple[int, ...], ...]:
    adjacency = _adjacency(geometry)
    answer: list[tuple[int, ...]] = []
    for source in range(geometry.n):
        distance = [-1] * geometry.n
        distance[source] = 0
        queue = deque([source])
        while queue:
            vertex = queue.popleft()
            for neighbour in adjacency[vertex]:
                if distance[neighbour] == -1:
                    distance[neighbour] = distance[vertex] + 1
                    queue.append(neighbour)
        assert all(value >= 0 for value in distance)
        answer.append(tuple(distance))
    return tuple(answer)


def _right_end_cut(geometry: Geometry, right_end: int) -> frozenset[int]:
    """The canonical corridor-left region at coordinate ``right_end-1``."""

    assert 1 <= right_end <= geometry.d
    coordinate = right_end - 1
    vertices = set(range(coordinate + 1))
    for component in geometry.components:
        if any(attachment <= coordinate for attachment in component.attachments):
            vertices.update(component.vertices)
    return frozenset(vertices)


def _cut_size(edges: tuple[Edge, ...], cut: frozenset[int]) -> int:
    return sum((a in cut) != (b in cut) for a, b in edges)


def _interval_multiplicities(geometry: Geometry) -> tuple[int, ...]:
    multiplicity = [0] * geometry.d
    for component in geometry.components:
        left, right = component.interval
        assert 0 <= left < right <= geometry.d
        assert min(component.attachments) == left
        assert max(component.attachments) == right
        for coordinate in range(left, right):
            multiplicity[coordinate] += 1
    return tuple(multiplicity)


def _rl_budget(s: int) -> int:
    # d=2s-1 is odd and at least nine here, so p(d)=1.
    return 5 * s * s + 2 * s


def _cut_feasible_set_check(
    candidates: tuple[tuple[int, int], ...],
    resources: tuple[int, ...],
    costs: tuple[int, ...],
    cut_count: int,
    budget: int,
) -> tuple[int, int]:
    """Exact 0/1 DP over every pairwise cut-capacity-feasible edge set.

    A state is ``(used_cut_mask, cardinality)``.  Its first field counts all
    represented subsets exactly, while its second field stores the largest
    quadratic cost among them.  Candidate identities are processed one by
    one, so equal resource masks still represent distinct internal edges.
    """

    assert len(candidates) == len(resources) == len(costs)
    states: dict[tuple[int, int], tuple[int, int]] = {(0, 0): (1, 0)}
    for resource, cost in zip(resources, costs, strict=True):
        assert 0 < resource < (1 << cut_count)
        updated = dict(states)
        for (used, cardinality), (count, largest_cost) in states.items():
            if used & resource:
                continue
            key = (used | resource, cardinality + 1)
            old_count, old_largest = updated.get(key, (0, -1))
            updated[key] = (old_count + count, max(old_largest, largest_cost + cost))
        states = updated
    feasible_count = 0
    largest_cost = -1
    for (_used, cardinality), (count, cost) in states.items():
        if cardinality >= 2:
            feasible_count += count
            largest_cost = max(largest_cost, cost)
    assert feasible_count > 0
    assert largest_cost <= budget
    return feasible_count, largest_cost


def check_geometry(geometry: Geometry) -> GeometryCheck:
    assert len(geometry.edges) == len(set(geometry.edges))
    assert len(geometry.selected_right_ends) == geometry.s - 1
    distances = _all_distances(geometry)
    assert distances[0][geometry.d] == geometry.d
    colours = tuple(distances[0][vertex] & 1 for vertex in range(geometry.n))
    assert all(colours[a] != colours[b] for a, b in geometry.edges)

    multiplicities = _interval_multiplicities(geometry)
    if geometry.kind == "mass":
        assert multiplicities == (1,) * geometry.d
        assert sorted(len(component.vertices) for component in geometry.components) == [
            1
        ] * (geometry.s - 2) + [2]
        assert sorted(right - left for left, right in (
            component.interval for component in geometry.components
        )) == [2] * (geometry.s - 2) + [3]
    else:
        assert geometry.kind == "overlap"
        assert multiplicities.count(2) == 1
        assert multiplicities.count(1) == geometry.d - 1
        assert all(len(component.vertices) == 1 for component in geometry.components)
        assert all(
            component.interval[1] - component.interval[0] == 2
            for component in geometry.components
        )

    cuts = tuple(
        _right_end_cut(geometry, right_end)
        for right_end in geometry.selected_right_ends
    )
    cut_sizes = tuple(_cut_size(geometry.edges, cut) for cut in cuts)
    assert all(0 in cut and geometry.d not in cut for cut in cuts)
    assert all(size <= 2 for size in cut_sizes)

    candidates: list[tuple[int, int]] = []
    resources: list[int] = []
    costs: list[int] = []
    pair_margins: list[int] = []
    levels = distances[0]
    adjacency = _adjacency(geometry)
    for first in range(geometry.n):
        for second in range(first + 1, geometry.n):
            distance = distances[first][second]
            if colours[first] != colours[second] or distance < 4:
                continue
            # A single internal edge at B-distance >=4 creates no triangle.
            assert not (adjacency[first] & adjacency[second])
            resource = 0
            for index, cut in enumerate(cuts):
                if (first in cut) != (second in cut):
                    resource |= 1 << index
            crossings = resource.bit_count()
            margin = 2 * crossings + 2 - distance
            assert margin >= 0
            # Independent route check: every legal pair is BFS-level aligned.
            assert distance == abs(levels[first] - levels[second])
            candidates.append((first, second))
            resources.append(resource)
            costs.append((distance + 1) ** 2)
            pair_margins.append(margin)

    assert candidates
    feasible_count, largest_cost = _cut_feasible_set_check(
        tuple(candidates),
        tuple(resources),
        tuple(costs),
        len(cuts),
        _rl_budget(geometry.s),
    )
    return GeometryCheck(
        legal_pairs=len(candidates),
        cut_feasible_sets_at_least_two=feasible_count,
        largest_cut_size=max(cut_sizes),
        least_pair_margin=min(pair_margins),
        largest_set_cost=largest_cost,
        set_budget_margin=_rl_budget(geometry.s) - largest_cost,
    )


def run_audit(s_values: Iterable[int] = range(5, 9)) -> AuditSummary:
    frozen_s_values = tuple(s_values)
    assert frozen_s_values
    geometries = tuple(all_geometries(frozen_s_values))
    checks = tuple(check_geometry(geometry) for geometry in geometries)
    mass_cases = sum(geometry.kind == "mass" for geometry in geometries)
    overlap_cases = sum(geometry.kind == "overlap" for geometry in geometries)
    return AuditSummary(
        verdict="PASS",
        s_values=frozen_s_values,
        mass_cases=mass_cases,
        overlap_cases=overlap_cases,
        geometry_cases=len(geometries),
        legal_pairs=sum(check.legal_pairs for check in checks),
        cut_feasible_sets_at_least_two=sum(
            check.cut_feasible_sets_at_least_two for check in checks
        ),
        largest_cut_size=max(check.largest_cut_size for check in checks),
        least_pair_margin=min(check.least_pair_margin for check in checks),
        least_set_budget_margin=min(check.set_budget_margin for check in checks),
    )


if __name__ == "__main__":
    print(json.dumps(asdict(run_audit()), sort_keys=True))
