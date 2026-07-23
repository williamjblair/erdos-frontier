"""Exact verifier for the Erdős #23 G-B series-composition reduction.

The route is deliberately narrower than the conjecture-strength 2-connected
core.  Two disjoint valid one-stub rooted blocks are joined by one B-edge
from the first stub terminal to the second root terminal.  The program checks
the cutwise validity composition, exact distance/slack accounting, and RL
budget superadditivity using integers only.
"""

from __future__ import annotations

import itertools
import pathlib
import sys
from typing import Iterable


HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from rl_lib import all_dists, check_rfc_direct, gamma_of, union_triangle_free  # noqa: E402


Edge = tuple[int, int]


def partner_distance(d: int) -> int:
    """The exact parity-minimal partner distance p(d), for d >= 1."""
    if d < 1:
        raise ValueError("stub distance must be positive")
    if d == 1:
        return 3
    return 2 if d % 2 == 0 else 1


def rl_budget(s: int, d: int) -> int:
    """RL right-hand side as a function of slack and stub distance."""
    if s < 0 or d < 1:
        raise ValueError("RL requires s >= 0 and d >= 1")
    return s * (2 * d + 2 + s) + 2 * s * partner_distance(d)


def separation(a: int, b: int) -> int:
    """0/1 indicator that two terminal membership bits differ."""
    if a not in (0, 1) or b not in (0, 1):
        raise ValueError("separation arguments must be bits")
    return int(a != b)


def cut_count(edges: Iterable[Edge], T: int) -> int:
    """Number of listed edges crossing the vertex subset encoded by T."""
    return sum(((T >> a) & 1) != ((T >> b) & 1) for a, b in edges)


def series_budget_margin(s1: int, d1: int, s2: int, d2: int) -> int:
    """Closed-form nonnegative margin in RL budget superadditivity.

    If D=d1+d2+1 and P=p(D), then the margin is

      2*s1*(s2+d2+1+P-p(d1)) + 2*s2*(d1+1+P-p(d2)).

    Each parenthesis is nonnegative because d1,d2 >= 1, 1 <= P, and
    p(di) <= 3.
    """
    if min(s1, s2) < 0 or min(d1, d2) < 1:
        raise ValueError("series parameters require si >= 0 and di >= 1")
    D = d1 + d2 + 1
    P = partner_distance(D)
    return (
        2 * s1 * (s2 + d2 + 1 + P - partner_distance(d1))
        + 2 * s2 * (d1 + 1 + P - partner_distance(d2))
    )


def _block(offset: int = 0) -> tuple[list[Edge], list[Edge], int, int]:
    """Seven-vertex exact rooted block from the frozen gate-3 fixtures.

    It is K_{2,1,2}-shaped at the level-set scale: root and stub are at
    distance four, one internal M-edge joins them, n=7, s=2, Gamma=25.
    """
    base_edges = [
        (0, 4),
        (1, 4),
        (2, 5),
        (3, 5),
        (0, 6),
        (1, 6),
        (2, 6),
        (3, 6),
    ]
    edges = [(a + offset, b + offset) for a, b in base_edges]
    M = [(4 + offset, 5 + offset)]
    return edges, M, 4 + offset, 5 + offset


def boundary_composite() -> dict[str, object]:
    """An exact n=14, |M|=2 composite in the open RL* middle regime."""
    edges1, M1, w1, x1 = _block(0)
    edges2, M2, w2, x2 = _block(7)
    bridge = (x1, w2)
    return {
        "n": 14,
        "edges": edges1 + edges2 + [bridge],
        "M": M1 + M2,
        "w": w1,
        "x0": x2,
        "bridge": bridge,
        "left_vertices": tuple(range(7)),
        "right_vertices": tuple(range(7, 14)),
        "edges1": edges1,
        "edges2": edges2,
        "M1": M1,
        "M2": M2,
        "w1": w1,
        "x1": x1,
        "w2": w2,
        "x2": x2,
    }


def _long_block(offset: int = 0) -> tuple[list[Edge], list[Edge], int, int]:
    """Ten-vertex rooted block with one internal edge at distance six."""
    base_edges = [
        (0, 6),
        (1, 6),
        (2, 7),
        (3, 7),
        (0, 8),
        (1, 8),
        (4, 8),
        (5, 8),
        (2, 9),
        (3, 9),
        (4, 9),
        (5, 9),
    ]
    edges = [(a + offset, b + offset) for a, b in base_edges]
    M = [(6 + offset, 7 + offset)]
    return edges, M, 6 + offset, 7 + offset


def mixed_distance_composite() -> dict[str, object]:
    """A mixed-even-distance n=17 series fixture with D-list [4,6]."""
    edges1, M1, w1, x1 = _block(0)
    edges2, M2, w2, x2 = _long_block(7)
    bridge = (x1, w2)
    return {
        "n": 17,
        "edges": edges1 + edges2 + [bridge],
        "M": M1 + M2,
        "w": w1,
        "x0": x2,
        "bridge": bridge,
        "left_vertices": tuple(range(7)),
        "right_vertices": tuple(range(7, 17)),
        "edges1": edges1,
        "edges2": edges2,
        "M1": M1,
        "M2": M2,
        "w1": w1,
        "x1": x1,
        "w2": w2,
        "x2": x2,
    }


def verify_boundary_composite() -> dict[str, int]:
    """Reproduce every exact claim made about the boundary composite."""
    F = boundary_composite()
    n = int(F["n"])
    edges = list(F["edges"])
    M = list(F["M"])
    w = int(F["w"])
    x0 = int(F["x0"])
    edges1 = list(F["edges1"])
    edges2 = list(F["edges2"])
    M1 = list(F["M1"])
    M2 = list(F["M2"])
    w1, x1 = int(F["w1"]), int(F["x1"])
    w2, x2 = int(F["w2"]), int(F["x2"])
    bridge = tuple(F["bridge"])

    if not union_triangle_free(n, edges, M):
        raise AssertionError("composite is not triangle-free")
    if check_rfc_direct(n, edges, M, w, x0) != (True, None):
        raise AssertionError("composite RFC failed")

    # Exact symmetric cut-condition audit.  This simultaneously verifies
    # each block, the bridge decomposition, the four-terminal separation
    # inequality, and the composite rooted condition for every global cut.
    min_slack = None
    for T in range(1 << n):
        bit = lambda v: (T >> v) & 1
        b1 = cut_count(edges1, T)
        b2 = cut_count(edges2, T)
        m1 = cut_count(M1, T)
        m2 = cut_count(M2, T)
        eb = separation(bit(bridge[0]), bit(bridge[1]))
        q1 = separation(bit(w1), bit(x1))
        q2 = separation(bit(w2), bit(x2))
        q = separation(bit(w1), bit(x2))

        if m1 + q1 > b1 or m2 + q2 > b2:
            raise AssertionError(f"local symmetric RFC failed at T={T}")
        if q > q1 + eb + q2:
            raise AssertionError(f"terminal separation inequality failed at T={T}")
        if cut_count(edges, T) != b1 + b2 + eb:
            raise AssertionError(f"B cut decomposition failed at T={T}")
        if cut_count(M, T) != m1 + m2:
            raise AssertionError(f"M cut decomposition failed at T={T}")
        global_slack = cut_count(edges, T) - cut_count(M, T) - q
        if global_slack < 0:
            raise AssertionError(f"global symmetric RFC failed at T={T}")
        min_slack = global_slack if min_slack is None else min(min_slack, global_slack)

    dist = all_dists(n, edges)
    d = dist[w][x0]
    s = n - 1 - d
    gamma = gamma_of(M, dist)
    if (d, s, gamma) != (9, 4, 50):
        raise AssertionError((d, s, gamma))
    if not 2 * s * partner_distance(d) < (d + 1) ** 2:
        raise AssertionError("fixture is not in the strict middle regime")

    d1 = all_dists(7, _block(0)[0])[4][5]
    # Shifted block has the same intrinsic metric.
    d2 = 4
    s1 = s2 = 2
    margin = series_budget_margin(s1, d1, s2, d2)
    if margin != rl_budget(s, d) - rl_budget(s1, d1) - rl_budget(s2, d2):
        raise AssertionError("series budget identity failed")

    return {
        "n": n,
        "m_edges": len(M),
        "d": d,
        "s": s,
        "gamma": gamma,
        "rfc_min_slack": int(min_slack),
        "series_budget_margin": margin,
        "global_rl_slack": rl_budget(s, d) - gamma,
        "cuts_checked": 1 << n,
    }


def verify_mixed_distance_composite() -> dict[str, object]:
    """Exact hostile check of the mixed-distance series fixture."""
    F = mixed_distance_composite()
    n = int(F["n"])
    edges = list(F["edges"])
    M = list(F["M"])
    w = int(F["w"])
    x0 = int(F["x0"])
    bridge = tuple(F["bridge"])
    if not union_triangle_free(n, edges, M):
        raise AssertionError("mixed composite is not triangle-free")
    if check_rfc_direct(n, edges, M, w, x0) != (True, None):
        raise AssertionError("mixed composite RFC failed")
    dist = all_dists(n, edges)
    distances = tuple(dist[a][b] for a, b in M)
    d = dist[w][x0]
    s = n - 1 - d
    gamma = gamma_of(M, dist)
    if (distances, d, s, gamma) != ((4, 6), 11, 5, 74):
        raise AssertionError((distances, d, s, gamma))
    if not 2 * s * partner_distance(d) < (d + 1) ** 2:
        raise AssertionError("mixed fixture is not in the middle regime")
    if cut_count(edges, sum(1 << v for v in F["left_vertices"])) != 1:
        raise AssertionError("advertised edge is not the unique bridge cut")
    s1, d1, s2, d2 = 2, 4, 3, 6
    return {
        "tuple": (n, len(M), d, s, gamma, rl_budget(s, d)),
        "M_distances": distances,
        "bridge": bridge,
        "component_sizes": (7, 10),
        "series_budget_margin": series_budget_margin(s1, d1, s2, d2),
        "global_rl_slack": rl_budget(s, d) - gamma,
    }


def exhaustive_arithmetic_audit() -> dict[str, int]:
    """Independent finite sweep over all parity and boundary patterns."""
    cases = 0
    min_margin = None
    for d1, d2, s1, s2 in itertools.product(
        range(1, 129), range(1, 129), range(0, 33), range(0, 33)
    ):
        direct = (
            rl_budget(s1 + s2, d1 + d2 + 1)
            - rl_budget(s1, d1)
            - rl_budget(s2, d2)
        )
        closed = series_budget_margin(s1, d1, s2, d2)
        if direct != closed or closed < 0:
            raise AssertionError((s1, d1, s2, d2, direct, closed))
        cases += 1
        min_margin = closed if min_margin is None else min(min_margin, closed)
    return {"arithmetic_cases": cases, "minimum_margin": int(min_margin)}


if __name__ == "__main__":
    print(verify_boundary_composite())
    print(verify_mixed_distance_composite())
    print(exhaustive_arithmetic_audit())
