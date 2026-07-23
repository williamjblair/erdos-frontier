"""Smaller fixed-demand CEGAR solver for the `(D4,D8), (s,d)=(5,8)` row."""

from __future__ import annotations

from dataclasses import dataclass

import z3

from compute23.gate2.common import adj_masks
from compute23.gate3.rl_lib import all_dists, check_rfc_direct
from compute23.gate3.agent_aggregation.solve_first_row_z3 import (
    N,
    PAIRS,
    P_EDGES,
    ROOT,
    STUB,
    _bridge_component_cut,
    _crosses,
)


@dataclass(frozen=True)
class FixedPairResult:
    status: str
    demand4: tuple[int, int]
    demand8: tuple[int, int]
    iterations: int
    rfc_cuts: int
    bridge_cuts: int
    b_edges: tuple[tuple[int, int], ...] | None


def solve_fixed_pair(
    demand4: tuple[int, int],
    demand8: tuple[int, int],
    *,
    max_iterations: int = 10000,
) -> FixedPairResult:
    demand4 = tuple(sorted(demand4))
    demand8 = tuple(sorted(demand8))
    assert demand4 in PAIRS and demand8 in PAIRS and demand4 != demand8
    solver = z3.Solver()
    b = {edge: z3.Bool(f"b_{edge[0]}_{edge[1]}") for edge in PAIRS}
    side = [z3.Bool(f"side_{v}") for v in range(N)]
    for vertex in range(9):
        solver.add(side[vertex] == z3.BoolVal(bool(vertex % 2)))
    for u, v in PAIRS:
        solver.add(z3.Implies(b[(u, v)], side[u] != side[v]))
    for edge in P_EDGES:
        solver.add(b[edge])
    for u, v in (demand4, demand8):
        solver.add(side[u] == side[v], z3.Not(b[(u, v)]))

    # Exact distances from just the three needed sources.
    source_targets = ((ROOT, STUB, 8), (demand4[0], demand4[1], 4),
                      (demand8[0], demand8[1], 8))
    for source_index, (source, target, target_distance) in enumerate(source_targets):
        distance = [z3.Int(f"d{source_index}_{v}") for v in range(N)]
        for vertex in range(N):
            solver.add(distance[vertex] >= 0, distance[vertex] <= N - 1)
            if vertex == source:
                solver.add(distance[vertex] == 0)
            else:
                solver.add(distance[vertex] >= 1)
                solver.add(
                    z3.Or(
                        [
                            z3.And(
                                b[tuple(sorted((vertex, neighbor)))],
                                distance[neighbor] + 1 == distance[vertex],
                            )
                            for neighbor in range(N)
                            if neighbor != vertex
                        ]
                    )
                )
        for u, v in PAIRS:
            solver.add(
                z3.Implies(
                    b[(u, v)],
                    z3.And(distance[u] <= distance[v] + 1,
                           distance[v] <= distance[u] + 1),
                )
            )
        solver.add(distance[target] == target_distance)

    rfc_cuts: set[int] = set()
    bridge_cuts: set[tuple[tuple[int, int], int]] = set()
    for iteration in range(1, max_iterations + 1):
        status = solver.check()
        if status == z3.unsat:
            return FixedPairResult("unsat", demand4, demand8, iteration,
                                   len(rfc_cuts), len(bridge_cuts), None)
        if status != z3.sat:
            return FixedPairResult(str(status), demand4, demand8, iteration,
                                   len(rfc_cuts), len(bridge_cuts), None)
        model = solver.model()
        b_edges = tuple(edge for edge in PAIRS if z3.is_true(model.eval(b[edge])))
        distances = all_dists(N, list(b_edges))
        assert distances[ROOT][STUB] == 8
        assert distances[demand4[0]][demand4[1]] == 4
        assert distances[demand8[0]][demand8[1]] == 8

        ok, bad_cut = check_rfc_direct(
            N, list(b_edges), [demand4, demand8], ROOT, STUB
        )
        if not ok:
            assert bad_cut is not None
            if bad_cut in rfc_cuts:
                raise AssertionError("repeated RFC counterexample")
            rfc_cuts.add(bad_cut)
            rhs = sum(_crosses(edge, bad_cut) for edge in (demand4, demand8))
            rhs += int(_crosses((ROOT, STUB), bad_cut))
            solver.add(
                z3.Sum(
                    [z3.If(b[edge], 1, 0) for edge in PAIRS
                     if _crosses(edge, bad_cut)]
                ) >= rhs
            )
            continue

        bad_bridge = None
        for edge in P_EDGES:
            component_cut = _bridge_component_cut(b_edges, edge)
            if component_cut is not None:
                bad_bridge = (edge, component_cut)
                break
        if bad_bridge is not None:
            if bad_bridge in bridge_cuts:
                raise AssertionError("repeated bridge counterexample")
            bridge_cuts.add(bad_bridge)
            edge, component_cut = bad_bridge
            solver.add(
                z3.Sum(
                    [z3.If(b[candidate], 1, 0) for candidate in PAIRS
                     if candidate != edge and _crosses(candidate, component_cut)]
                ) >= 1
            )
            continue

        return FixedPairResult("sat", demand4, demand8, iteration,
                               len(rfc_cuts), len(bridge_cuts), b_edges)
    return FixedPairResult("iteration_limit", demand4, demand8, max_iterations,
                           len(rfc_cuts), len(bridge_cuts), None)


if __name__ == "__main__":
    print(solve_fixed_pair((7, 10), (11, 13)))
