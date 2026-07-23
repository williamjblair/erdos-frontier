"""Inspect weighted RFC cut duals on one dense distance-four complement.

The instance selection exactly reproduces the deterministic search in
``agent_aggregation/explore_private_complement.py`` and stops at its first
``n=15,d=5,s=9`` private-completion complement.  HiGHS is used only to
discover a support.  Reported rational weights are then checked with
``fractions.Fraction`` against every primal column and the exact objective.
"""

from __future__ import annotations

import random
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))

from compute23.gate2.common import adj_masks, bfs_dist
from compute23.gate3.agent_aggregation.explore_private_complement import (
    canonical_path_is_all_nonbridge,
    random_bipartite,
)
from compute23.gate3.agent_aggregation.quotient_cut_average import canonical_geodesic
from compute23.gate3.rl_lib import (
    all_dists,
    m_candidates,
    p_of_d,
    rl_rhs,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)


def find_fixture() -> dict[str, object]:
    rng = random.Random(230711)
    for trial in range(3000):
        n = rng.randint(14, 16)
        b_edges = random_bipartite(rng, n)
        if not b_edges:
            continue
        adjacency = adj_masks(n, b_edges)
        if any(distance < 0 for distance in bfs_dist(n, adjacency, 0)):
            continue
        distances = all_dists(n, b_edges)
        candidates = m_candidates(n, distances)
        if len(candidates) < 2:
            continue
        bit = xor_bits(n)
        supply = np.zeros(1 << n, dtype=np.int32)
        for u, v in b_edges:
            supply += bit[u] ^ bit[v]
        for sample in range(4):
            size = rng.randint(2, min(4, len(candidates)))
            m_edges = tuple(sorted(rng.sample(candidates, size)))
            if not union_triangle_free(n, b_edges, m_edges):
                continue
            slack = supply.copy()
            for u, v in m_edges:
                slack -= bit[u] ^ bit[v]
            if slack.min() < 0:
                continue
            valid = valid_stub_pairs(n, slack)
            m_distances = tuple(distances[u][v] for u, v in m_edges)
            endpoint_count = len({vertex for edge in m_edges for vertex in edge})
            private_order = endpoint_count + sum(distance - 1 for distance in m_distances)
            for root in range(n):
                for stub in range(n):
                    if not valid[root][stub]:
                        continue
                    d = distances[root][stub]
                    s = n - 1 - d
                    if not (
                        s >= 5
                        and d < 2 * s
                        and 2 * s * p_of_d(d) < (d + 1) ** 2
                    ):
                        continue
                    path = canonical_geodesic(n, b_edges, root, stub)
                    if not canonical_path_is_all_nonbridge(n, b_edges, path):
                        continue
                    if private_order**2 <= rl_rhs(n, d):
                        continue
                    if (n, d, s) == (15, 5, 9) and set(m_distances) == {4}:
                        return {
                            "trial": trial,
                            "sample": sample,
                            "n": n,
                            "B": tuple(b_edges),
                            "M": m_edges,
                            "w": root,
                            "x0": stub,
                            "path": path,
                            "dist": distances,
                        }
    raise AssertionError("deterministic complement fixture not found")


def cut_rows(n: int, b_edges, demands, w: int, x0: int):
    rows: list[list[int]] = []
    bounds: list[int] = []
    masks: list[int] = []
    for mask in range(1 << n):
        if (mask >> w) & 1:
            continue
        supply = sum((((mask >> u) ^ (mask >> v)) & 1) for u, v in b_edges)
        terminal = (mask >> x0) & 1
        rows.append([(((mask >> u) ^ (mask >> v)) & 1) for u, v in demands])
        bounds.append(supply - terminal)
        masks.append(mask)
    return rows, bounds, masks


def rational(value: float) -> Fraction:
    result = Fraction(value).limit_denominator(10000)
    assert abs(float(result) - value) < 1e-7, (value, result)
    return result


def solve_and_audit(label: str, fixture: dict[str, object], demands) -> None:
    n = int(fixture["n"])
    b_edges = fixture["B"]
    w = int(fixture["w"])
    x0 = int(fixture["x0"])
    dist = fixture["dist"]
    rows, bounds, masks = cut_rows(n, b_edges, demands, w, x0)
    costs = [(dist[u][v] + 1) ** 2 for u, v in demands]
    matrix = np.asarray(rows + [[-1] * len(demands)], dtype=float)
    rhs = np.asarray(bounds + [-2], dtype=float)
    answer = linprog(
        -np.asarray(costs, dtype=float),
        A_ub=matrix,
        b_ub=rhs,
        bounds=[(0, None)] * len(demands),
        method="highs",
    )
    assert answer.success, answer.message

    marginals = [-value for value in answer.ineqlin.marginals]
    cut_weights = [rational(value) for value in marginals[:-1]]
    reserve = rational(marginals[-1])
    support = [(masks[i], weight) for i, weight in enumerate(cut_weights) if weight]

    for column, cost in enumerate(costs):
        separation = sum(
            weight * rows[row][column] for row, weight in enumerate(cut_weights)
        )
        assert separation >= cost + reserve, (demands[column], separation, cost, reserve)
    exact_dual = sum(weight * bound for weight, bound in zip(cut_weights, bounds)) - 2 * reserve
    exact_primal = sum(rational(value) * cost for value, cost in zip(answer.x, costs))
    assert exact_dual == exact_primal

    levels = dist[w]
    level_masks = {
        sum(1 << vertex for vertex in range(n) if levels[vertex] >= threshold)
        for threshold in range(1, max(levels) + 1)
    }
    stars = {
        1 << vertex for vertex in range(n) if vertex != w
    }
    print(label)
    print("demands", tuple((edge, dist[edge[0]][edge[1]]) for edge in demands))
    print("primal_support", tuple((demands[i], rational(value)) for i, value in enumerate(answer.x) if value > 1e-8))
    print("reserve", reserve, "objective", exact_dual, "budget", rl_rhs(n, dist[w][x0]))
    print(
        "cut_support",
        tuple(
            (
                mask,
                tuple(vertex for vertex in range(n) if (mask >> vertex) & 1),
                weight,
                "BFS_LEVEL" if mask in level_masks else "VERTEX_STAR" if mask in stars else "ARBITRARY",
                bounds[masks.index(mask)],
            )
            for mask, weight in support
        ),
    )


def main() -> None:
    fixture = find_fixture()
    print(
        "fixture",
        {key: value for key, value in fixture.items() if key != "dist"},
    )
    solve_and_audit("ACTUAL_M", fixture, fixture["M"])
    all_candidates = tuple(m_candidates(int(fixture["n"]), fixture["dist"]))
    solve_and_audit("ALL_CANDIDATES", fixture, all_candidates)


if __name__ == "__main__":
    main()
