"""Exact structural enumerator for the Erdős 23 ``d = 2s-2`` row.

The Lean module ``Erdos23GapGBTwoDefect`` proves that only seven refined
integer-interval types survive bipartiteness:

* pure mass: one size-three block;
* pure mass: two size-two blocks;
* mixed mass/span;
* mixed mass/overlap;
* pure span;
* pure overlap: one duplicated interval;
* pure overlap: two one-edge overlaps.

This checker constructs every position of those types for ``4 <= s <= 8``
and every bipartite-compatible optional attachment in the exceptional
blocks.  It verifies the exact interval ledger, BFS profile, adjacent-extra
bound, and every legal same-side pair.  It is falsification support, not a
replacement for the quantified Lean classification or graph-alignment
proofs.
"""

from __future__ import annotations

from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations, product
import json
from typing import Iterable


Edge = tuple[int, int]


@dataclass(frozen=True)
class Block:
    kind: str
    start: int
    span: int
    option: int = 0


@dataclass(frozen=True)
class Geometry:
    shape: str
    s: int
    d: int
    blocks: tuple[Block, ...]


@dataclass(frozen=True)
class BuiltGeometry:
    geometry: Geometry
    n: int
    edges: tuple[Edge, ...]
    labels: tuple[str, ...]
    intervals: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class Check:
    legal_pairs: int
    aligned_pairs: int
    unaligned_pairs: int
    outside_pairs: int
    adjacent_extra: int
    capacity_sum: int
    fully_aligned: bool
    unaligned_types: tuple[tuple[str, int], ...]


@dataclass(frozen=True)
class Summary:
    verdict: str
    s_values: tuple[int, ...]
    geometry_cases: int
    cases_by_shape: tuple[tuple[str, int], ...]
    fully_aligned_cases: int
    fully_aligned_by_shape: tuple[tuple[str, int], ...]
    nonaligned_by_shape: tuple[tuple[str, int], ...]
    legal_pairs: int
    aligned_pairs: int
    unaligned_pairs: int
    outside_pairs: int
    largest_adjacent_extra: int
    largest_capacity_excess: int
    unaligned_types: tuple[tuple[str, int], ...]


def _edge(a: int, b: int) -> Edge:
    assert a != b
    return (a, b) if a < b else (b, a)


def _normalise(edges: Iterable[Edge]) -> tuple[Edge, ...]:
    result = tuple(sorted({_edge(a, b) for a, b in edges}))
    return result


def _partition_blocks(lengths: tuple[int, ...], kinds: tuple[str, ...],
                      options: tuple[int, ...]) -> tuple[Block, ...]:
    assert len(lengths) == len(kinds) == len(options)
    cursor = 0
    blocks = []
    for length, kind, option in zip(lengths, kinds, options, strict=True):
        blocks.append(Block(kind, cursor, length, option))
        cursor += length
    return tuple(blocks)


def _overlap_blocks(lengths: tuple[int, ...], kinds: tuple[str, ...],
                    options: tuple[int, ...], overlap: int) -> tuple[Block, ...]:
    assert 0 <= overlap < len(lengths) - 1
    starts = [0]
    for index, length in enumerate(lengths[:-1]):
        starts.append(starts[-1] + length - (index == overlap))
    return tuple(
        Block(kind, start, length, option)
        for kind, start, length, option in zip(
            kinds, starts, lengths, options, strict=True
        )
    )


def geometries(s_values: Iterable[int] = range(4, 9)) -> Iterable[Geometry]:
    for s in s_values:
        d = 2 * s - 2
        # Pure mass: one q=3, span-four block.
        count = s - 2
        for exceptional in range(count):
            lengths = tuple(4 if i == exceptional else 2 for i in range(count))
            kinds = tuple("q3s4" if i == exceptional else "q1s2" for i in range(count))
            for option in range(16):
                options = tuple(option if i == exceptional else 0 for i in range(count))
                yield Geometry("mass_q3", s, d,
                               _partition_blocks(lengths, kinds, options))

        # Pure mass: two q=2, span-three blocks.
        for first, second in combinations(range(count), 2):
            lengths = tuple(3 if i in (first, second) else 2 for i in range(count))
            kinds = tuple("q2s3" if i in (first, second) else "q1s2" for i in range(count))
            for first_option, second_option in product(range(4), repeat=2):
                options = tuple(
                    first_option if i == first else
                    second_option if i == second else 0
                    for i in range(count)
                )
                yield Geometry("mass_q2_q2", s, d,
                               _partition_blocks(lengths, kinds, options))

        # Mixed mass/span: one q=2 component in a span-two tile.
        count = s - 1
        for exceptional in range(count):
            kinds = tuple("q2s2" if i == exceptional else "q1s2" for i in range(count))
            for option in range(2):
                options = tuple(option if i == exceptional else 0 for i in range(count))
                yield Geometry("mass_span", s, d,
                               _partition_blocks((2,) * count, kinds, options))

        # Mixed mass/overlap: one q=2 span-three block and one overlap step.
        for exceptional in range(count):
            lengths = tuple(3 if i == exceptional else 2 for i in range(count))
            kinds = tuple("q2s3" if i == exceptional else "q1s2" for i in range(count))
            for overlap in range(count - 1):
                for option in range(4):
                    options = tuple(option if i == exceptional else 0 for i in range(count))
                    yield Geometry(
                        "mass_overlap", s, d,
                        _overlap_blocks(lengths, kinds, options, overlap),
                    )

        # Pure span: a tiled corridor and one span-zero singleton attachment.
        base = tuple(Block("q1s2", 2 * i, 2) for i in range(s - 1))
        for attachment in range(d + 1):
            yield Geometry("pure_span", s, d,
                           base + (Block("q1s0", attachment, 0),))

        # Pure overlap: one duplicate start (step zero).
        for duplicate in range(s - 1):
            starts = [0]
            for transition in range(s - 1):
                starts.append(starts[-1] + (0 if transition == duplicate else 2))
            blocks = tuple(Block("q1s2", start, 2) for start in starts)
            yield Geometry("overlap_duplicate", s, d, blocks)

        # Pure overlap: two one-edge overlap steps.
        for first, second in combinations(range(s - 1), 2):
            starts = [0]
            for transition in range(s - 1):
                starts.append(starts[-1] + (1 if transition in (first, second) else 2))
            blocks = tuple(Block("q1s2", start, 2) for start in starts)
            yield Geometry("overlap_two", s, d, blocks)


def build(geometry: Geometry) -> BuiltGeometry:
    d = geometry.d
    edges: list[Edge] = [(i, i + 1) for i in range(d)]
    labels = [f"p{i}" for i in range(d + 1)]
    intervals = []
    next_vertex = d + 1
    for block_index, block in enumerate(geometry.blocks):
        a = block.start
        if block.kind == "q1s2":
            vertex = next_vertex
            next_vertex += 1
            labels.append(f"q1[{block_index}]@{a}")
            edges.extend(((vertex, a), (vertex, a + 2)))
            intervals.append((a, a + 2))
        elif block.kind == "q1s0":
            vertex = next_vertex
            next_vertex += 1
            labels.append(f"leaf@{a}")
            edges.append((vertex, a))
            intervals.append((a, a))
        elif block.kind == "q2s3":
            left, right = next_vertex, next_vertex + 1
            next_vertex += 2
            labels.extend((f"q2L[{block_index}]@{a}", f"q2R[{block_index}]@{a}"))
            edges.extend(((left, right), (left, a), (right, a + 3)))
            if block.option & 1:
                edges.append((right, a + 1))
            if block.option & 2:
                edges.append((left, a + 2))
            intervals.append((a, a + 3))
        elif block.kind == "q2s2":
            anchor, tip = next_vertex, next_vertex + 1
            next_vertex += 2
            labels.extend((f"q2A[{block_index}]@{a}", f"q2T[{block_index}]@{a}"))
            edges.extend(((anchor, tip), (anchor, a), (anchor, a + 2)))
            if block.option:
                edges.append((tip, a + 1))
            intervals.append((a, a + 2))
        elif block.kind == "q3s4":
            left, middle, right = next_vertex, next_vertex + 1, next_vertex + 2
            next_vertex += 3
            labels.extend((
                f"q3L[{block_index}]@{a}",
                f"q3M[{block_index}]@{a}",
                f"q3R[{block_index}]@{a}",
            ))
            edges.extend(((left, middle), (middle, right), (left, a), (right, a + 4)))
            optional = ((middle, a + 1), (left, a + 2),
                        (right, a + 2), (middle, a + 3))
            for bit, edge in enumerate(optional):
                if (block.option >> bit) & 1:
                    edges.append(edge)
            intervals.append((a, a + 4))
        else:
            raise AssertionError(block.kind)
    assert next_vertex == 3 * geometry.s - 1
    return BuiltGeometry(
        geometry=geometry,
        n=next_vertex,
        edges=_normalise(edges),
        labels=tuple(labels),
        intervals=tuple(intervals),
    )


def _adjacency(built: BuiltGeometry) -> tuple[frozenset[int], ...]:
    adjacency = [set() for _ in range(built.n)]
    for a, b in built.edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    return tuple(frozenset(row) for row in adjacency)


def _distances(built: BuiltGeometry) -> tuple[tuple[int, ...], ...]:
    adjacency = _adjacency(built)
    rows = []
    for source in range(built.n):
        distance = [-1] * built.n
        distance[source] = 0
        queue = deque([source])
        while queue:
            vertex = queue.popleft()
            for neighbour in adjacency[vertex]:
                if distance[neighbour] == -1:
                    distance[neighbour] = distance[vertex] + 1
                    queue.append(neighbour)
        assert all(value >= 0 for value in distance)
        rows.append(tuple(distance))
    return tuple(rows)


def _type(label: str) -> str:
    if label.startswith("p"):
        return "path"
    if label.startswith("leaf"):
        return "leaf"
    return label.split("[")[0]


def check(geometry: Geometry) -> Check:
    built = build(geometry)
    distances = _distances(built)
    d, s = geometry.d, geometry.s
    assert distances[0][d] == d
    levels = distances[0]
    colours = tuple(level & 1 for level in levels)
    assert all(colours[a] != colours[b] for a, b in built.edges)

    multiplicity = [0] * d
    total_span = 0
    total_mass = 0
    span_defect = 0
    for left, right in built.intervals:
        assert 0 <= left <= right <= d
        total_span += right - left
        for coordinate in range(left, right):
            multiplicity[coordinate] += 1
    for block in geometry.blocks:
        mass = {
            "q1s2": 1,
            "q1s0": 1,
            "q2s3": 2,
            "q2s2": 2,
            "q3s4": 3,
        }[block.kind]
        total_mass += mass
        span_defect += mass + 1 - block.span
    assert all(value >= 1 for value in multiplicity)
    assert total_mass == s
    defects = (s - len(geometry.blocks), span_defect, total_span - d)
    expected_defects = {
        "mass_q3": (2, 0, 0),
        "mass_q2_q2": (2, 0, 0),
        "mass_span": (1, 1, 0),
        "mass_overlap": (1, 0, 1),
        "pure_span": (0, 2, 0),
        "overlap_duplicate": (0, 0, 2),
        "overlap_two": (0, 0, 2),
    }[geometry.shape]
    assert defects == expected_defects
    assert sum(defects) == 2
    if geometry.shape == "mass_overlap":
        assert multiplicity.count(2) == 1 and max(multiplicity) == 2
    elif geometry.shape in ("overlap_duplicate", "overlap_two"):
        assert multiplicity.count(2) == 2 and max(multiplicity) == 2
    else:
        assert multiplicity == [1] * d

    layer_count = Counter(levels)
    extras = [layer_count[level] - 1 for level in range(d + 1)]
    assert all(value >= 0 for value in extras)
    weight = sum(extras[r] + extras[r + 1] for r in range(d))
    adjacent = sum(extras[r] * extras[r + 1] for r in range(d))
    capacity_sum = weight + adjacent
    assert weight <= 2 * s
    assert adjacent <= 2
    assert capacity_sum <= 2 * s + 2
    for a, b in built.edges:
        assert abs(levels[a] - levels[b]) == 1

    legal = aligned = outside = 0
    unaligned_types: Counter[str] = Counter()
    for first in range(built.n):
        for second in range(first + 1, built.n):
            distance = distances[first][second]
            if colours[first] != colours[second] or distance < 4:
                continue
            legal += 1
            if levels[first] > d or levels[second] > d:
                outside += 1
                key = "/".join(sorted((_type(built.labels[first]), _type(built.labels[second]))))
                unaligned_types[f"outside:{geometry.shape}:{key}"] += 1
            elif distance == abs(levels[first] - levels[second]):
                aligned += 1
            else:
                key = "/".join(sorted((_type(built.labels[first]), _type(built.labels[second]))))
                unaligned_types[f"unaligned:{geometry.shape}:{key}"] += 1
    unaligned = legal - aligned - outside
    return Check(
        legal_pairs=legal,
        aligned_pairs=aligned,
        unaligned_pairs=unaligned,
        outside_pairs=outside,
        adjacent_extra=adjacent,
        capacity_sum=capacity_sum,
        fully_aligned=(unaligned == 0 and outside == 0),
        unaligned_types=tuple(sorted(unaligned_types.items())),
    )


def run(s_values: Iterable[int] = range(4, 9)) -> Summary:
    frozen = tuple(s_values)
    cases = tuple(geometries(frozen))
    checks = tuple(check(case) for case in cases)
    shape_counts = Counter(case.shape for case in cases)
    aligned_shape_counts = Counter(
        case.shape for case, result in zip(cases, checks, strict=True)
        if result.fully_aligned
    )
    nonaligned_shape_counts = shape_counts - aligned_shape_counts
    type_counts: Counter[str] = Counter()
    for result in checks:
        type_counts.update(dict(result.unaligned_types))
    return Summary(
        verdict="PASS",
        s_values=frozen,
        geometry_cases=len(cases),
        cases_by_shape=tuple(sorted(shape_counts.items())),
        fully_aligned_cases=sum(result.fully_aligned for result in checks),
        fully_aligned_by_shape=tuple(sorted(aligned_shape_counts.items())),
        nonaligned_by_shape=tuple(sorted(nonaligned_shape_counts.items())),
        legal_pairs=sum(result.legal_pairs for result in checks),
        aligned_pairs=sum(result.aligned_pairs for result in checks),
        unaligned_pairs=sum(result.unaligned_pairs for result in checks),
        outside_pairs=sum(result.outside_pairs for result in checks),
        largest_adjacent_extra=max(result.adjacent_extra for result in checks),
        largest_capacity_excess=max(
            result.capacity_sum - 2 * case.s
            for case, result in zip(cases, checks, strict=True)
        ),
        unaligned_types=tuple(sorted(type_counts.items())),
    )


if __name__ == "__main__":
    print(json.dumps(asdict(run()), sort_keys=True))
