"""Exact hostile substrate for the remaining Erdős 23 G-B aggregation.

This module does not claim RL*.  It freezes the residual-regime predicate,
reproduces the mandatory killed aggregation fixtures, and exposes the exact
series-induction size gate used by the endpoint-near bridge route.
"""

from __future__ import annotations

from dataclasses import dataclass

from compute23.gate2.common import (
    adj_masks,
    all_max_cuts,
    b_connected,
    c5_blowup,
    parse_graph6,
    split_edges,
)
from compute23.gate3.rl_lib import (
    all_dists,
    check_rfc_direct,
    gamma_of,
    geodesics_between,
    p_of_d,
    rl_rhs,
)


Edge = tuple[int, int]


@dataclass(frozen=True)
class RootedMetrics:
    n: int
    d: int
    s: int
    m_distances: tuple[int, ...]
    gamma: int
    rl_budget: int
    rfc_valid: bool


@dataclass(frozen=True)
class ColoredFixture:
    n: int
    all_edges: tuple[Edge, ...]
    b_edges: tuple[Edge, ...]
    m_edges: tuple[Edge, ...]
    m_distances: tuple[int, ...]
    gamma: int
    forced_hub_load: int


def residual_regime(n: int, d: int, m_count: int) -> bool:
    """The exact strict RL* residual predicate from the campaign prompt."""

    s = n - 1 - d
    return (
        n >= 14
        and d >= 3
        and s >= 2
        and m_count >= 2
        and 2 * s * p_of_d(d) < (d + 1) ** 2
    )


def rooted_metrics(
    *,
    n: int,
    b_edges: tuple[Edge, ...] | list[Edge],
    m_edges: tuple[Edge, ...] | list[Edge],
    root: int,
    stub: int,
) -> RootedMetrics:
    """Reproduce every numerical field of a one-stub rooted instance."""

    b_edges = tuple(tuple(sorted(e)) for e in b_edges)
    m_edges = tuple(tuple(sorted(e)) for e in m_edges)
    assert b_connected(n, list(b_edges))
    distances = all_dists(n, list(b_edges))
    m_distances = tuple(sorted(distances[u][v] for u, v in m_edges))
    assert all(d >= 4 and d % 2 == 0 for d in m_distances)
    valid, _ = check_rfc_direct(
        n, list(b_edges), list(m_edges), root, stub
    )
    d = distances[root][stub]
    return RootedMetrics(
        n=n,
        d=d,
        s=n - 1 - d,
        m_distances=m_distances,
        gamma=gamma_of(list(m_edges), distances),
        rl_budget=rl_rhs(n, d),
        rfc_valid=valid,
    )


def _forced_hub_load(
    n: int, b_edges: tuple[Edge, ...], m_edges: tuple[Edge, ...]
) -> int:
    adjacency = adj_masks(n, list(b_edges))
    distances = all_dists(n, list(b_edges))
    paths = {
        edge: geodesics_between(n, adjacency, distances, *edge)
        for edge in m_edges
    }
    return max(
        sum(
            distances[u][v] + 1
            for (u, v), edge_paths in paths.items()
            if edge_paths and all(x in path for path in edge_paths)
        )
        for x in range(n)
    )


def colored_fixture(graph6: str, cut: int) -> ColoredFixture:
    """Decode one mandatory unrooted falsification fixture exactly."""

    n, edges = parse_graph6(graph6)
    m_edges, b_edges = split_edges(edges, cut)
    distances = all_dists(n, b_edges)
    m_distances = tuple(sorted(distances[u][v] for u, v in m_edges))
    return ColoredFixture(
        n=n,
        all_edges=tuple(edges),
        b_edges=tuple(b_edges),
        m_edges=tuple(m_edges),
        m_distances=m_distances,
        gamma=gamma_of(m_edges, distances),
        forced_hub_load=_forced_hub_load(
            n, tuple(b_edges), tuple(m_edges)
        ),
    )


def build_long_tail_c5_fixture(
    q: int, tail_length: int
) -> dict[str, object]:
    """Attach a rooted B-path to a balanced C5 blow-up maximum cut.

    This family is RFC-valid and kills the uncorrected global bound
    ``sum D_i <= 2s`` even inside the strict residual regime.
    """

    assert q >= 1 and tail_length >= 1
    base_n, all_edges, _ = c5_blowup([q] * 5)
    chosen = None
    for cut in all_max_cuts(base_n, all_edges)[1]:
        m_edges, b_edges = split_edges(all_edges, cut)
        if not b_connected(base_n, b_edges):
            continue
        distances = all_dists(base_n, b_edges)
        if m_edges and all(distances[u][v] == 4 for u, v in m_edges):
            chosen = (m_edges, b_edges)
            break
    assert chosen is not None
    m_edges, b_edges = chosen
    root = 0
    tail = list(range(base_n, base_n + tail_length))
    path_edges = [(root, tail[0])]
    path_edges.extend((tail[i], tail[i + 1]) for i in range(len(tail) - 1))
    return {
        "n": base_n + tail_length,
        "b_edges": tuple(b_edges + path_edges),
        "m_edges": tuple(m_edges),
        "root": root,
        "stub": tail[-1],
    }


def joint_distance_excess(m_distances: tuple[int, ...]) -> int:
    return sum(d - 4 for d in m_distances)


def exact_series_induction_gate(
    *, n1: int, n2: int, d1: int, d2: int
) -> bool:
    """Exact replacement for the old sufficient gate ``n1,n2 >= 4``."""

    return (
        n1 + p_of_d(d1) < n1 + n2
        and n2 + p_of_d(d2) < n1 + n2
    )


def residual_series_dispatch(
    *, n1: int, n2: int, d1: int, d2: int
) -> str:
    """Classify a residual interior bridge by the proved exact dispatch.

    The caller supplies genuine component data: both local distances are
    positive and each geodesic fits in its component.  In the strict middle
    regime the result is either ``"induction"`` (the exact minimal-composite
    gate passes) or ``"endpoint_pair"`` (a two-vertex endpoint component,
    hence an M-free endpoint leaf).
    """

    assert d1 >= 1 and d2 >= 1
    assert d1 + 1 <= n1 and d2 + 1 <= n2
    n = n1 + n2
    d = d1 + d2 + 1
    assert residual_regime(n, d, m_count=2)
    if exact_series_induction_gate(n1=n1, n2=n2, d1=d1, d2=d2):
        return "induction"
    assert n1 == 2 or n2 == 2
    return "endpoint_pair"


def endpoint_move_budget_nonincrease(*, s: int, d: int) -> bool:
    """Exact arithmetic for root move/stub retraction at distance ``d``."""

    assert s >= 0 and d >= 2
    before = s * (2 * d + 2 + s) + 2 * s * p_of_d(d)
    after = s * (2 * (d - 1) + 2 + s) + 2 * s * p_of_d(d - 1)
    return after <= before


def endpoint_gamma_block_absorbs(*, order: int, s: int, d: int) -> bool:
    """Exact endpoint-bridge absorption with a Gamma-controlled block."""

    assert order >= 2 and s >= 0 and d >= 1
    local = s * (2 * d + 2 + s) + 2 * s * p_of_d(d)
    whole_s = s + order - 1
    whole_d = d + 1
    whole = (
        whole_s * (2 * whole_d + 2 + whole_s)
        + 2 * whole_s * p_of_d(whole_d)
    )
    return order**2 + local <= whole


def threshold_separation_sum(a: int, b: int, height: int) -> int:
    """Exact finite layer-cake count used by the RFC potential dual."""

    assert 0 <= a <= height and 0 <= b <= height
    return sum((k < a) != (k < b) for k in range(height))


def double_slack_resource_certificate(
    *, s: int, distances: tuple[int, ...], resources: tuple[int, ...]
) -> bool:
    """Exact ``d=2s`` resource-packing implication banked in Lean."""

    assert s >= 5 and len(distances) == len(resources)
    assert all(r >= 1 for r in resources)
    assert sum(resources) <= s - 1
    assert all(d <= 2 * r + 2 for d, r in zip(distances, resources))
    return sum((d + 1) ** 2 for d in distances) <= (
        s * (2 * (2 * s) + 2 + s) + 2 * s * p_of_d(2 * s)
    )


if __name__ == "__main__":
    tail = rooted_metrics(**build_long_tail_c5_fixture(3, 5))
    print(
        {
            "long_tail": tail,
            "sum_distance": sum(tail.m_distances),
            "two_slack": 2 * tail.s,
            "double_broom": colored_fixture("G?`F`w", 15),
            "path_packing": colored_fixture("K??E@_qi?]Ia", 63),
        }
    )
