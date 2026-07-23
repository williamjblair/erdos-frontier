"""Probe whether the raw RFC cut LP already implies the BF-RL objective.

This is a falsification tool only.  For each connected bipartite supply graph
``B`` and root/stub pair, it maximizes the quadratic-distance coefficient
linearly over fractional demand multiplicities subject to every rooted cut
constraint, box constraints, and total demand mass at least two.  A value
above ``rl_rhs`` refutes closure by a cut-dual certificate that ignores
integrality and the triangle constraints among demand edges.
"""

from __future__ import annotations

import argparse

import numpy as np
from scipy.optimize import linprog

from compute23.gate3.rl_lib import (
    all_dists,
    gen_bipartite,
    m_candidates,
    parse_graph6,
    rl_rhs,
)


def cut_rows(n: int, edges, candidates, w: int, x0: int):
    """Return ``A, b`` for all root-excluding RFC cuts ``A x <= b``."""
    rows = []
    bounds = []
    for mask in range(1 << n):
        if (mask >> w) & 1:
            continue
        bcut = sum(
            ((mask >> a) & 1) != ((mask >> b) & 1) for a, b in edges
        )
        stub = (mask >> x0) & 1
        capacity = bcut - stub
        assert capacity >= 0
        rows.append(
            [
                int(((mask >> a) & 1) != ((mask >> b) & 1))
                for a, b in candidates
            ]
        )
        bounds.append(capacity)
    return np.asarray(rows, dtype=float), np.asarray(bounds, dtype=float)


def fractional_optimum(
    n: int, edges, candidates, dist, w: int, x0: int, *, box: bool
):
    """Return the fractional maximum, or ``None`` when mass two is infeasible."""
    if len(candidates) < 2:
        return None
    A, b = cut_rows(n, edges, candidates, w, x0)
    # The last row encodes sum x_e >= 2.
    A = np.vstack([A, -np.ones(len(candidates))])
    b = np.append(b, -2.0)
    cost = np.asarray(
        [(dist[a][bb] + 1) ** 2 for a, bb in candidates], dtype=float
    )
    result = linprog(
        -cost,
        A_ub=A,
        b_ub=b,
        bounds=[(0.0, 1.0 if box else None)] * len(candidates),
        method="highs",
    )
    if result.status == 2:
        return None
    if not result.success:
        raise RuntimeError(result.message)
    return -result.fun, result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("nmax", type=int, nargs="?", default=0)
    parser.add_argument("--residual-numerics", action="store_true")
    parser.add_argument("--no-box", action="store_true")
    parser.add_argument("--show-best", action="store_true")
    parser.add_argument("--diamonds", type=int)
    parser.add_argument("--overlap", nargs=2, type=int, metavar=("S", "D"))
    parser.add_argument("--long-tail", nargs=2, type=int, metavar=("Q", "T"))
    args = parser.parse_args()
    if args.long_tail is not None:
        from compute23.gate3.gap_gb_joint_verify import build_long_tail_c5_fixture

        q, tail_length = args.long_tail
        fixture = build_long_tail_c5_fixture(q, tail_length)
        n = fixture["n"]
        edges = list(fixture["b_edges"])
        w = fixture["root"]
        x0 = fixture["stub"]
        dist = all_dists(n, edges)
        candidates = m_candidates(n, dist)
        optimum = fractional_optimum(
            n,
            edges,
            candidates,
            dist,
            w,
            x0,
            box=not args.no_box,
        )
        if optimum is None:
            print("LONG-TAIL infeasible")
            return
        value, result = optimum
        d = dist[w][x0]
        support = [
            (candidates[i], d if False else dist[candidates[i][0]][candidates[i][1]], float(x))
            for i, x in enumerate(result.x)
            if x > 1e-8
        ]
        print(
            "LONG-TAIL",
            f"q={q}",
            f"tail={tail_length}",
            f"n={n}",
            f"d={d}",
            f"candidates={len(candidates)}",
            f"value={value:.12g}",
            f"budget={rl_rhs(n, d)}",
            f"support={support}",
        )
        return
    if args.diamonds is not None or args.overlap is not None:
        if args.diamonds is not None:
            s = args.diamonds
            d = 2 * s
            starts = [2 * k for k in range(s)]
            label = "DIAMONDS"
        else:
            s, d = args.overlap
            assert 2 <= d <= 2 * s
            starts = list(range(0, d - 1, 2))
            if d % 2 == 1:
                starts.append(d - 2)
            starts = starts[:s]
            starts += [starts[i % len(starts)] for i in range(s - len(starts))]
            label = "OVERLAP"
        n = d + 1 + s
        edges = [(i, i + 1) for i in range(d)]
        edges += [(starts[k], d + 1 + k) for k in range(s)]
        edges += [(d + 1 + k, starts[k] + 2) for k in range(s)]
        dist = all_dists(n, edges)
        candidates = m_candidates(n, dist)
        optimum = fractional_optimum(
            n,
            edges,
            candidates,
            dist,
            0,
            d,
            box=not args.no_box,
        )
        if optimum is None:
            print(f"{label} infeasible")
            return
        value, result = optimum
        support = [
            (candidates[i], dist[candidates[i][0]][candidates[i][1]], float(x))
            for i, x in enumerate(result.x)
            if x > 1e-8
        ]
        print(
            label,
            f"s={s}",
            f"d={d}",
            f"n={n}",
            f"candidates={len(candidates)}",
            f"value={value:.12g}",
            f"budget={rl_rhs(n, d)}",
            f"support={support}",
        )
        return
    checked = 0
    best = None
    for n in range(5, args.nmax + 1):
        for graph6 in gen_bipartite(n):
            nn, edges = parse_graph6(graph6)
            assert nn == n
            dist = all_dists(n, edges)
            candidates = m_candidates(n, dist)
            if len(candidates) < 2:
                continue
            for w in range(n):
                for x0 in range(n):
                    if w == x0:
                        continue
                    d = dist[w][x0]
                    if args.residual_numerics:
                        s = n - 1 - d
                        p = 3 if d == 1 else 2 if d % 2 == 0 else 1
                        if not (5 <= s and d <= 2 * s and 2 * s * p < (d + 1) ** 2):
                            continue
                    optimum = fractional_optimum(
                        n,
                        edges,
                        candidates,
                        dist,
                        w,
                        x0,
                        box=not args.no_box,
                    )
                    if optimum is None:
                        continue
                    checked += 1
                    value, result = optimum
                    vector = result.x
                    budget = rl_rhs(n, d)
                    ratio = value / budget if budget else float("inf")
                    if best is None or ratio > best[0]:
                        best = (
                            ratio,
                            n,
                            graph6,
                            edges,
                            candidates,
                            dist,
                            w,
                            x0,
                            d,
                            value,
                            budget,
                            result,
                        )
                    if value > budget + 1e-7:
                        support = [
                            (candidates[i], float(x))
                            for i, x in enumerate(vector)
                            if x > 1e-8
                        ]
                        print(
                            "CUT-LP VIOLATION",
                            f"n={n}",
                            f"g6={graph6}",
                            f"w={w}",
                            f"x0={x0}",
                            f"d={d}",
                            f"value={value:.12g}",
                            f"budget={budget}",
                            f"support={support}",
                        )
                        return
        print(f"n={n}: checked={checked}", flush=True)
    print(f"NO CUT-LP VIOLATION; checked={checked}")
    if args.show_best and best is not None:
        (
            ratio,
            n,
            graph6,
            edges,
            candidates,
            dist,
            w,
            x0,
            d,
            value,
            budget,
            result,
        ) = best
        support = [
            (candidates[i], dist[candidates[i][0]][candidates[i][1]], float(x))
            for i, x in enumerate(result.x)
            if x > 1e-8
        ]
        # HiGHS reports minimization marginals; negate them to obtain the
        # nonnegative maximization weights on our RFC rows.
        dual = [
            (i, float(-weight))
            for i, weight in enumerate(result.ineqlin.marginals)
            if abs(weight) > 1e-8
        ]
        print(
            "BEST",
            f"ratio={ratio:.12g}",
            f"n={n}",
            f"g6={graph6}",
            f"edges={edges}",
            f"w={w}",
            f"x0={x0}",
            f"d={d}",
            f"value={value:.12g}",
            f"budget={budget}",
            f"support={support}",
            f"dual={dual}",
        )


if __name__ == "__main__":
    main()
