#!/usr/bin/env python3
"""Exact hostile probe for the pure-mass isometric-cut route.

The tempting structural claim is that disjoint saturated canonical blocks
form a chain of even cycles, hence admit ``d`` size-two cut coordinates.
The constructors in ``agent_d2s`` include every bipartite-compatible extra
attachment inside the exceptional size-two/size-three blocks, so they are a
direct stress test of that claim.

For each constructor this script:

* computes the Djokovic edge relation and checks whether it is transitive;
* records whether all resulting coordinates are literal size-two cuts; and
* solves the complete rooted cut-condition integer program for a maximum
  total legal-demand distance, with at least two demands.

The integer-program result is then checked independently against every cut.
The small-corpus pass additionally scans every unlabeled bipartite graph on
eight vertices for a geodesic with the literal pure-mass interval ledger and
checks every valid two-demand rooted instance on that geometry.

This is falsification support.  A zero-failure output is not an unbounded
proof of the surviving distance-sum inequality.
"""

from __future__ import annotations

import argparse
from collections import Counter, deque
from dataclasses import asdict, dataclass
from itertools import combinations
import json
from typing import Iterable

import numpy as np
from z3 import Int, Solver, Sum, sat

from compute23.gate2.common import adj_masks, parse_graph6
from compute23.gate3.agent_d2s.two_defect_geometry_verify import (
    BuiltGeometry,
    Geometry,
    _distances,
    build,
    geometries,
)
from compute23.gate3.rl_lib import (
    all_dists,
    gen_bipartite,
    geodesics_between,
    m_candidates,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


Demand = tuple[int, int, int]


@dataclass(frozen=True)
class OptimisationResult:
    feasible: bool
    candidate_count: int
    constraint_count: int
    maximum_distance_sum: int
    chosen: tuple[Demand, ...]


@dataclass(frozen=True)
class CutCertificate:
    feasible: bool
    total_weight: int
    available_cut_count: int
    positive_weight_count: int
    weights: tuple[tuple[tuple[int, ...], int], ...]


def _inside(mask: int, vertex: int) -> bool:
    """Membership in a root-avoiding cut; vertex zero is the root."""

    return vertex > 0 and bool((mask >> (vertex - 1)) & 1)


def _legal_demands(built: BuiltGeometry) -> tuple[Demand, ...]:
    distances = _distances(built)
    colours = tuple(distance & 1 for distance in distances[0])
    return tuple(
        (u, v, distances[u][v])
        for u in range(built.n)
        for v in range(u + 1, built.n)
        if colours[u] == colours[v] and distances[u][v] >= 4
    )


def _cut_constraints(
    built: BuiltGeometry, candidates: tuple[Demand, ...]
) -> dict[tuple[int, bool], int]:
    """Return the strongest capacity for each exact separation signature."""

    constraints: dict[tuple[int, bool], int] = {}
    for mask in range(1 << (built.n - 1)):
        capacity = sum(
            _inside(mask, u) != _inside(mask, v) for u, v in built.edges
        )
        signature = 0
        for index, (u, v, _distance) in enumerate(candidates):
            if _inside(mask, u) != _inside(mask, v):
                signature |= 1 << index
        key = (signature, _inside(mask, built.geometry.d))
        constraints[key] = min(capacity, constraints.get(key, capacity))
    return constraints


def maximise_rfc_distance_sum(built: BuiltGeometry) -> OptimisationResult:
    """Solve the exact binary RFC programme and recheck the returned model."""

    candidates = _legal_demands(built)
    constraints = _cut_constraints(built, candidates)
    variables = tuple(Int(f"demand_{index}") for index in range(len(candidates)))
    base = Solver()
    for variable in variables:
        base.add(variable >= 0, variable <= 1)
    base.add(Sum(variables) >= 2)
    for (signature, stub_inside), capacity in constraints.items():
        separated = [
            variables[index]
            for index in range(len(variables))
            if (signature >> index) & 1
        ]
        base.add(Sum(separated) + int(stub_inside) <= capacity)

    if base.check() != sat:
        return OptimisationResult(
            feasible=False,
            candidate_count=len(candidates),
            constraint_count=len(constraints),
            maximum_distance_sum=-1,
            chosen=(),
        )

    objective = Sum(
        [distance * variables[index]
         for index, (_u, _v, distance) in enumerate(candidates)]
    )
    low, high = 0, sum(distance for _u, _v, distance in candidates)
    while low < high:
        middle = (low + high + 1) // 2
        base.push()
        base.add(objective >= middle)
        feasible = base.check() == sat
        base.pop()
        if feasible:
            low = middle
        else:
            high = middle - 1
    base.add(objective == low)
    assert base.check() == sat
    model = base.model()
    chosen = tuple(
        candidates[index]
        for index, variable in enumerate(variables)
        if model.eval(variable).as_long() == 1
    )
    assert len(chosen) >= 2
    assert sum(distance for _u, _v, distance in chosen) == low

    # Independent exhaustive cut check of the solver witness.
    for mask in range(1 << (built.n - 1)):
        capacity = sum(
            _inside(mask, u) != _inside(mask, v) for u, v in built.edges
        )
        demand_load = sum(
            _inside(mask, u) != _inside(mask, v) for u, v, _distance in chosen
        )
        assert demand_load + _inside(mask, built.geometry.d) <= capacity

    return OptimisationResult(
        feasible=True,
        candidate_count=len(candidates),
        constraint_count=len(constraints),
        maximum_distance_sum=low,
        chosen=chosen,
    )


def theta_diagnostics(built: BuiltGeometry) -> dict[str, object]:
    """Compute the Djokovic relation and its transitive-closure classes."""

    distances = _distances(built)
    edges = built.edges
    relation = [[False] * len(edges) for _ in edges]
    for first, (u, v) in enumerate(edges):
        for second, (x, y) in enumerate(edges):
            relation[first][second] = (
                distances[u][x] + distances[v][y]
                != distances[u][y] + distances[v][x]
            )

    seen: set[int] = set()
    classes: list[tuple[int, ...]] = []
    for start in range(len(edges)):
        if start in seen:
            continue
        seen.add(start)
        stack = [start]
        component: list[int] = []
        while stack:
            edge_index = stack.pop()
            component.append(edge_index)
            for other in range(len(edges)):
                if relation[edge_index][other] and other not in seen:
                    seen.add(other)
                    stack.append(other)
        classes.append(tuple(sorted(component)))

    closure_class = {
        edge_index: class_index
        for class_index, edge_class in enumerate(classes)
        for edge_index in edge_class
    }
    transitive = all(
        relation[first][second]
        == (closure_class[first] == closure_class[second])
        for first in range(len(edges))
        for second in range(len(edges))
    )

    cut_data = []
    for edge_class in classes:
        removed = set(edge_class)
        adjacency = [[] for _ in range(built.n)]
        for index, (u, v) in enumerate(edges):
            if index not in removed:
                adjacency[u].append(v)
                adjacency[v].append(u)
        component = [-1] * built.n
        component_count = 0
        for start in range(built.n):
            if component[start] >= 0:
                continue
            component[start] = component_count
            queue = deque([start])
            while queue:
                vertex = queue.popleft()
                for neighbour in adjacency[vertex]:
                    if component[neighbour] < 0:
                        component[neighbour] = component_count
                        queue.append(neighbour)
            component_count += 1
        cut_data.append(
            {
                "size": len(edge_class),
                "component_count": component_count,
                "separates_terminals": (
                    component[0] != component[built.geometry.d]
                ),
                "edges": tuple(edges[index] for index in edge_class),
            }
        )

    return {
        "theta_transitive": transitive,
        "class_count": len(classes),
        "class_sizes": tuple(sorted(len(edge_class) for edge_class in classes)),
        "all_size_two_terminal_cuts": transitive and all(
            item["size"] == 2
            and item["component_count"] == 2
            and item["separates_terminals"]
            for item in cut_data
        ),
        "cut_data": tuple(cut_data),
    }


def _small_terminal_cut_masks(built: BuiltGeometry) -> tuple[int, ...]:
    """Enumerate every root/stub-separating cut of capacity at most two."""

    masks: set[int] = set()
    edge_indices = range(len(built.edges))
    for removed_count in range(3):
        for removed_tuple in combinations(edge_indices, removed_count):
            removed = set(removed_tuple)
            adjacency = [[] for _ in range(built.n)]
            for index, (u, v) in enumerate(built.edges):
                if index in removed:
                    continue
                adjacency[u].append(v)
                adjacency[v].append(u)
            component = [-1] * built.n
            component_count = 0
            for start in range(built.n):
                if component[start] >= 0:
                    continue
                component[start] = component_count
                queue = deque([start])
                while queue:
                    vertex = queue.popleft()
                    for neighbour in adjacency[vertex]:
                        if component[neighbour] < 0:
                            component[neighbour] = component_count
                            queue.append(neighbour)
                component_count += 1
            root_component = component[0]
            stub_component = component[built.geometry.d]
            if root_component == stub_component:
                continue
            optional_components = tuple(
                index
                for index in range(component_count)
                if index not in {root_component, stub_component}
            )
            for optional_mask in range(1 << len(optional_components)):
                chosen_components = {stub_component}
                chosen_components.update(
                    optional_components[index]
                    for index in range(len(optional_components))
                    if (optional_mask >> index) & 1
                )
                cut_vertices = {
                    vertex
                    for vertex in range(built.n)
                    if component[vertex] in chosen_components
                }
                capacity = sum(
                    (u in cut_vertices) != (v in cut_vertices)
                    for u, v in built.edges
                )
                if capacity > 2:
                    continue
                mask = sum(
                    1 << (vertex - 1)
                    for vertex in cut_vertices
                    if vertex > 0
                )
                masks.add(mask)
    return tuple(sorted(masks))


def dominating_two_cut_certificate(
    built: BuiltGeometry, total_weight: int | None = None
) -> CutCertificate:
    """Find ``d`` repeated size-two cuts dominating all legal distances."""

    if total_weight is None:
        total_weight = built.geometry.d

    cuts = _small_terminal_cut_masks(built)
    candidates = _legal_demands(built)
    weights = tuple(Int(f"cut_weight_{index}") for index in range(len(cuts)))
    solver = Solver()
    for weight in weights:
        solver.add(weight >= 0)
    solver.add(Sum(weights) == total_weight)
    for u, v, distance in candidates:
        separating_weights = [
            weight
            for mask, weight in zip(cuts, weights, strict=True)
            if _inside(mask, u) != _inside(mask, v)
        ]
        solver.add(Sum(separating_weights) >= distance)
    if solver.check() != sat:
        return CutCertificate(False, total_weight, len(cuts), 0, ())
    model = solver.model()
    positive = tuple(
        (
            tuple(
                vertex
                for vertex in range(1, built.n)
                if _inside(mask, vertex)
            ),
            model.eval(weight).as_long(),
        )
        for mask, weight in zip(cuts, weights, strict=True)
        if model.eval(weight).as_long() > 0
    )
    assert sum(weight for _cut, weight in positive) == total_weight
    for u, v, distance in candidates:
        separation_weight = sum(
            weight
            for cut, weight in positive
            if (u in cut) != (v in cut)
        )
        assert distance <= separation_weight
    for cut, _weight in positive:
        cut_set = set(cut)
        assert built.geometry.d in cut_set and 0 not in cut_set
        assert sum(
            (u in cut_set) != (v in cut_set) for u, v in built.edges
        ) <= 2
    return CutCertificate(
        True, total_weight, len(cuts), len(positive), positive
    )


def find_small_rfc_distance_sum_failure(
    built: BuiltGeometry,
) -> tuple[Demand, ...] | None:
    """Find an exact two/three-demand witness with total distance above d."""

    candidates = _legal_demands(built)
    bits = xor_bits(built.n)
    residual = np.zeros(1 << built.n, dtype=np.int16)
    for u, v in built.edges:
        residual += bits[u] ^ bits[v]
    residual -= bits[0] ^ bits[built.geometry.d]
    demand_cuts = tuple(bits[u] ^ bits[v] for u, v, _distance in candidates)
    compatible = [[False] * len(candidates) for _ in candidates]
    for first in range(len(candidates)):
        for second in range(first + 1, len(candidates)):
            if int((
                residual - demand_cuts[first] - demand_cuts[second]
            ).min()) < 0:
                continue
            compatible[first][second] = compatible[second][first] = True
            pair = (candidates[first], candidates[second])
            if sum(distance for _u, _v, distance in pair) > built.geometry.d:
                return pair
    for first in range(len(candidates)):
        for second in range(first + 1, len(candidates)):
            if not compatible[first][second]:
                continue
            for third in range(second + 1, len(candidates)):
                if not (
                    compatible[first][third] and compatible[second][third]
                ):
                    continue
                if int((
                    residual
                    - demand_cuts[first]
                    - demand_cuts[second]
                    - demand_cuts[third]
                ).min()) < 0:
                    continue
                triple = (
                    candidates[first], candidates[second], candidates[third]
                )
                if sum(
                    distance for _u, _v, distance in triple
                ) > built.geometry.d:
                    return triple
    return None


def constructor_probe(
    max_s: int, optimise_rfc: bool = True, find_rfc_witness: bool = True
) -> dict[str, object]:
    counts: Counter[str] = Counter()
    first: dict[str, object] = {}
    maximum_excess: int | None = None
    for geometry in geometries(range(3, max_s + 1)):
        if geometry.shape not in {"mass_q3", "mass_q2_q2"}:
            continue
        counts["constructors"] += 1
        counts[f"constructors_s{geometry.s}"] += 1
        counts[f"constructors_{geometry.shape}"] += 1
        built = build(geometry)
        theta = theta_diagnostics(built)
        if not theta["theta_transitive"]:
            counts["non_partial_cube"] += 1
            first.setdefault(
                "non_partial_cube",
                {"geometry": asdict(geometry), "edges": built.edges, "theta": theta},
            )
        if not theta["all_size_two_terminal_cuts"]:
            counts["not_size_two_basis"] += 1
            first.setdefault(
                "not_size_two_basis",
                {"geometry": asdict(geometry), "edges": built.edges, "theta": theta},
            )

        certificate = dominating_two_cut_certificate(built)
        if certificate.feasible:
            counts["dominating_two_cut_certificates"] += 1
            first.setdefault(
                f"certificate_{geometry.shape}",
                {
                    "geometry": asdict(geometry),
                    "edges": built.edges,
                    "certificate": asdict(certificate),
                },
            )
        else:
            counts["dominating_two_cut_failures"] += 1
            first.setdefault(
                "dominating_two_cut_failure",
                {"geometry": asdict(geometry), "edges": built.edges},
            )
            repaired_certificate = dominating_two_cut_certificate(
                built, geometry.d + 2
            )
            if repaired_certificate.feasible:
                counts["dominating_two_cut_plus_two_repairs"] += 1
                first.setdefault(
                    "dominating_two_cut_plus_two_repair",
                    {
                        "geometry": asdict(geometry),
                        "edges": built.edges,
                        "certificate": asdict(repaired_certificate),
                    },
                )
            else:
                counts["dominating_two_cut_plus_two_failures"] += 1
            witness = (
                find_small_rfc_distance_sum_failure(built)
                if find_rfc_witness
                else None
            )
            if witness is not None:
                counts["pure_mass_sum_bound_failures"] += 1
                first.setdefault(
                    "pure_mass_sum_bound_failure",
                    {
                        "geometry": asdict(geometry),
                        "edges": built.edges,
                        "demands": witness,
                        "distance_sum": sum(
                            distance for _u, _v, distance in witness
                        ),
                    },
                )

        if not optimise_rfc:
            continue
        optimum = maximise_rfc_distance_sum(built)
        if not optimum.feasible:
            counts["no_two_demand_rfc_family"] += 1
            continue
        excess = optimum.maximum_distance_sum - geometry.d
        maximum_excess = (
            excess if maximum_excess is None else max(maximum_excess, excess)
        )
        if excess > 0:
            counts["distance_sum_failures"] += 1
            first.setdefault(
                "distance_sum_failure",
                {
                    "geometry": asdict(geometry),
                    "edges": built.edges,
                    "optimisation": asdict(optimum),
                },
            )
        if excess == 0:
            counts["distance_sum_equalities"] += 1
    return {
        "max_s": max_s,
        "counts": dict(counts),
        "maximum_distance_sum_minus_d": maximum_excess,
        "first": first,
    }


def _pure_mass_path(
    n: int, adjacency_masks: tuple[int, ...], path: tuple[int, ...]
) -> bool:
    d = len(path) - 1
    s = n - d - 1
    support = set(path)
    outside = set(range(n)) - support
    components: list[set[int]] = []
    while outside:
        start = next(iter(outside))
        outside.remove(start)
        component = {start}
        queue = deque([start])
        while queue:
            vertex = queue.popleft()
            neighbours = {
                candidate
                for candidate in tuple(outside)
                if (adjacency_masks[vertex] >> candidate) & 1
            }
            outside.difference_update(neighbours)
            component.update(neighbours)
            queue.extend(neighbours)
        components.append(component)
    if len(components) != s - 2:
        return False

    covered: set[int] = set()
    total_span = 0
    for component in components:
        attachment_indices = {
            index
            for index, path_vertex in enumerate(path)
            if any((adjacency_masks[path_vertex] >> vertex) & 1
                   for vertex in component)
        }
        if len(attachment_indices) < 2:
            return False
        left, right = min(attachment_indices), max(attachment_indices)
        span = right - left
        if span != len(component) + 1:
            return False
        interval = set(range(left, right))
        if covered & interval:
            return False
        covered.update(interval)
        total_span += span
    return total_span == d and covered == set(range(d))


def rooted_small_corpus() -> dict[str, object]:
    """Scan the only nontrivial pure-mass order at n <= 9: n=8,s=3,d=4."""

    n = 8
    bits = xor_bits(n)
    counts: Counter[str] = Counter()
    first: dict[str, object] = {}
    for graph6 in gen_bipartite(n):
        nn, edges = parse_graph6(graph6)
        assert nn == n
        distances = all_dists(n, edges)
        adjacency = adj_masks(n, edges)
        pure_pairs: list[tuple[int, int]] = []
        for root in range(n):
            for stub in range(n):
                if distances[root][stub] != 4:
                    continue
                paths = geodesics_between(n, adjacency, distances, root, stub)
                if any(_pure_mass_path(n, adjacency, tuple(path)) for path in paths):
                    pure_pairs.append((root, stub))
        if not pure_pairs:
            continue
        counts["graphs"] += 1
        counts["root_stub_geometries"] += len(pure_pairs)

        candidates = m_candidates(n, distances)
        supply = np.zeros(1 << n, dtype=np.int16)
        for u, v in edges:
            supply += bits[u] ^ bits[v]
        demand_cuts = {
            edge: bits[edge[0]] ^ bits[edge[1]] for edge in candidates
        }
        for demands in combinations(candidates, 2):
            if not union_triangle_free(n, edges, demands):
                continue
            slack = supply.copy()
            for demand in demands:
                slack -= demand_cuts[demand]
            if int(slack.min()) < 0:
                continue
            roots = valid_stub_pairs(n, slack)
            distance_sum = sum(distances[u][v] for u, v in demands)
            for root, stub in pure_pairs:
                if not roots[root][stub]:
                    continue
                counts["valid_two_demand_instances"] += 1
                if distance_sum > 4:
                    counts["distance_sum_failures"] += 1
                    first.setdefault(
                        "distance_sum_failure",
                        {
                            "graph6": graph6,
                            "edges": edges,
                            "demands": demands,
                            "root": root,
                            "stub": stub,
                            "distances": tuple(
                                distances[u][v] for u, v in demands
                            ),
                        },
                    )
                if distance_sum == 4:
                    counts["distance_sum_equalities"] += 1
    return {"n": n, "counts": dict(counts), "first": first}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-s", type=int, default=5)
    parser.add_argument("--skip-corpus", action="store_true")
    parser.add_argument("--skip-rfc-optimisation", action="store_true")
    parser.add_argument("--skip-rfc-witness", action="store_true")
    args = parser.parse_args()
    result = {
        "constructors": constructor_probe(
            args.max_s,
            optimise_rfc=not args.skip_rfc_optimisation,
            find_rfc_witness=not args.skip_rfc_witness,
        )
    }
    if not args.skip_corpus:
        result["rooted_small_corpus"] = rooted_small_corpus()
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
