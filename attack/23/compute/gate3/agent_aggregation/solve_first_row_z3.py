"""CEGAR feasibility solver for the first dangerous multiset-gate row.

Question: is there a 14-vertex connected bipartite supply graph with a fixed
0--8 geodesic of length 8, all eight corridor edges nonbridges, one demand at
distance four, one at distance eight, and RFC for the stub pair (0,8)?

Z3 carries exact all-pairs graph distances.  RFC and nonbridge cuts are added
lazily from exact counterexamples until a model passes or the finite formula
is UNSAT.  This is a discovery/certification aid, not a paper proof.
"""

from __future__ import annotations

from dataclasses import dataclass

import z3

from compute23.gate2.common import adj_masks, bfs_dist
from compute23.gate3.rl_lib import all_dists, check_rfc_direct


N = 14
ROOT = 0
STUB = 8
P_EDGES = tuple((i, i + 1) for i in range(8))
PAIRS = tuple((u, v) for u in range(N) for v in range(u + 1, N))


@dataclass(frozen=True)
class FirstRowModel:
    b_edges: tuple[tuple[int, int], ...]
    m_edges: tuple[tuple[int, int], tuple[int, int]]
    rfc_cuts_added: int
    bridge_cuts_added: int
    iterations: int


def _crosses(edge: tuple[int, int], cut: int) -> bool:
    u, v = edge
    return ((cut >> u) & 1) != ((cut >> v) & 1)


def _bridge_component_cut(
    edges: tuple[tuple[int, int], ...], removed: tuple[int, int]
) -> int | None:
    adjacency = adj_masks(N, [edge for edge in edges if edge != removed])
    reached = 1 << removed[0]
    stack = [removed[0]]
    while stack:
        u = stack.pop()
        neighbors = adjacency[u]
        while neighbors:
            v = (neighbors & -neighbors).bit_length() - 1
            neighbors &= neighbors - 1
            if not ((reached >> v) & 1):
                reached |= 1 << v
                stack.append(v)
    return reached if not ((reached >> removed[1]) & 1) else None


def solve_first_row(*, max_iterations: int | None = None) -> FirstRowModel | None:
    solver = z3.Solver()
    b = {edge: z3.Bool(f"b_{edge[0]}_{edge[1]}") for edge in PAIRS}
    m4 = {edge: z3.Bool(f"m4_{edge[0]}_{edge[1]}") for edge in PAIRS}
    m8 = {edge: z3.Bool(f"m8_{edge[0]}_{edge[1]}") for edge in PAIRS}
    side = [z3.Bool(f"side_{v}") for v in range(N)]
    root_dist = [z3.Int(f"root_dist_{v}") for v in range(N)]

    for vertex in range(9):
        solver.add(side[vertex] == z3.BoolVal(bool(vertex % 2)))
    for edge in PAIRS:
        u, v = edge
        solver.add(z3.Implies(b[edge], side[u] != side[v]))
    for edge in P_EDGES:
        solver.add(b[edge])

    # Exact root distances ensure connectivity and make the fixed corridor a
    # geodesic.  Edge-Lipschitz labels lower-bound every path; predecessors
    # construct paths of the labeled lengths.
    for vertex in range(N):
        solver.add(root_dist[vertex] >= 0, root_dist[vertex] <= N - 1)
        if vertex == ROOT:
            solver.add(root_dist[vertex] == 0)
        else:
            solver.add(root_dist[vertex] >= 1)
            solver.add(
                z3.Or(
                    [
                        z3.And(
                            b[tuple(sorted((vertex, neighbor)))],
                            root_dist[neighbor] + 1 == root_dist[vertex],
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
                z3.And(
                    root_dist[u] <= root_dist[v] + 1,
                    root_dist[v] <= root_dist[u] + 1,
                ),
            )
        )
    solver.add(root_dist[STUB] == 8)

    # Exact bounded reachability through length eight.  `reach[k][u][v]`
    # means that a B-walk of length at most k joins u and v.
    reach = [
        [[z3.Bool(f"reach_{k}_{u}_{v}") for v in range(N)] for u in range(N)]
        for k in range(9)
    ]
    for u in range(N):
        for v in range(N):
            solver.add(reach[0][u][v] == z3.BoolVal(u == v))
    for k in range(1, 9):
        for u in range(N):
            for v in range(N):
                extensions = []
                for x in range(N):
                    if x == v:
                        continue
                    extensions.append(
                        z3.And(reach[k - 1][u][x], b[tuple(sorted((x, v)))])
                    )
                solver.add(
                    reach[k][u][v]
                    == z3.Or(reach[k - 1][u][v], z3.Or(extensions))
                )

    solver.add(z3.PbEq([(m4[edge], 1) for edge in PAIRS], 1))
    solver.add(z3.PbEq([(m8[edge], 1) for edge in PAIRS], 1))
    for edge in PAIRS:
        u, v = edge
        solver.add(z3.Not(z3.And(m4[edge], m8[edge])))
        solver.add(
            z3.Implies(
                m4[edge],
                z3.And(side[u] == side[v], reach[4][u][v], z3.Not(reach[3][u][v])),
            )
        )
        solver.add(
            z3.Implies(
                m8[edge],
                z3.And(side[u] == side[v], reach[8][u][v], z3.Not(reach[7][u][v])),
            )
        )

    rfc_cuts_added: set[int] = set()
    bridge_cuts_added: set[tuple[int, int]] = set()
    iterations = 0
    while max_iterations is None or iterations < max_iterations:
        iterations += 1
        status = solver.check()
        if status == z3.unsat:
            return None
        if status != z3.sat:
            raise RuntimeError(status)
        model = solver.model()
        b_edges = tuple(edge for edge in PAIRS if z3.is_true(model.eval(b[edge])))
        demand4 = next(edge for edge in PAIRS if z3.is_true(model.eval(m4[edge])))
        demand8 = next(edge for edge in PAIRS if z3.is_true(model.eval(m8[edge])))
        m_edges = (demand4, demand8)

        # Independent exact graph-distance reproduction guards the encoding.
        actual_distances = all_dists(N, list(b_edges))
        assert actual_distances[ROOT][STUB] == 8
        assert actual_distances[demand4[0]][demand4[1]] == 4
        assert actual_distances[demand8[0]][demand8[1]] == 8

        rfc_ok, bad_cut = check_rfc_direct(N, list(b_edges), list(m_edges), ROOT, STUB)
        if not rfc_ok:
            assert bad_cut is not None and bad_cut not in rfc_cuts_added
            rfc_cuts_added.add(bad_cut)
            supply = z3.Sum([z3.If(b[edge], 1, 0) for edge in PAIRS if _crosses(edge, bad_cut)])
            demand = z3.Sum(
                [z3.If(m4[edge], 1, 0) + z3.If(m8[edge], 1, 0)
                 for edge in PAIRS if _crosses(edge, bad_cut)]
            )
            stub_cross = int(_crosses((ROOT, STUB), bad_cut))
            solver.add(demand + stub_cross <= supply)
            continue

        bad_bridge = None
        for edge in P_EDGES:
            component_cut = _bridge_component_cut(b_edges, edge)
            if component_cut is not None:
                bad_bridge = (edge, component_cut)
                break
        if bad_bridge is not None:
            edge, component_cut = bad_bridge
            key = (edge[0], component_cut)
            assert key not in bridge_cuts_added
            bridge_cuts_added.add(key)
            alternatives = [
                z3.If(b[candidate], 1, 0)
                for candidate in PAIRS
                if candidate != edge and _crosses(candidate, component_cut)
            ]
            solver.add(z3.Sum(alternatives) >= 1)
            continue

        return FirstRowModel(
            b_edges=b_edges,
            m_edges=m_edges,
            rfc_cuts_added=len(rfc_cuts_added),
            bridge_cuts_added=len(bridge_cuts_added),
            iterations=iterations,
        )
    raise TimeoutError(
        (iterations, len(rfc_cuts_added), len(bridge_cuts_added))
    )


if __name__ == "__main__":
    print(solve_first_row())
