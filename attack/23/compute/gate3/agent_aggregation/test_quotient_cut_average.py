from __future__ import annotations

from itertools import combinations

import numpy as np

from compute23.gate2.common import parse_graph6
from compute23.gate3.gap_gb_joint_verify import (
    build_long_tail_c5_fixture,
    colored_fixture,
)
from compute23.gate3.gap_gb_series_verify import mixed_distance_composite
from compute23.gate3.rl_lib import (
    all_dists,
    gen_bipartite,
    m_candidates,
    union_triangle_free,
    valid_stub_pairs,
    xor_bits,
)

from compute23.gate3.agent_aggregation.quotient_cut_average import (
    all_path_subset_margins,
    canonical_geodesic,
    quotient_cut_bound,
)


def _path_tail_fixture(base_n: int, b_edges, m_edges, tail_length: int):
    root = 0
    tail = list(range(base_n, base_n + tail_length))
    edges = list(b_edges) + [(root, tail[0])] + list(zip(tail, tail[1:]))
    return {
        "n": base_n + tail_length,
        "b_edges": tuple(edges),
        "m_edges": tuple(m_edges),
        "path": tuple([root] + tail),
    }


def test_short_fat_and_long_thin_equality_families() -> None:
    fat = build_long_tail_c5_fixture(q=3, tail_length=5)
    fat_path = canonical_geodesic(fat["n"], fat["b_edges"], fat["root"], fat["stub"])
    fat_record = quotient_cut_bound(
        n=fat["n"],
        b_edges=fat["b_edges"],
        m_edges=fat["m_edges"],
        path=fat_path,
        reproduce_all_component_cuts=True,
    )
    assert fat_record.attachments <= 2 * fat_record.s
    assert min(
        all_path_subset_margins(
            n=fat["n"],
            b_edges=fat["b_edges"],
            m_edges=fat["m_edges"],
            path=fat_path,
            reproduce_all_component_cuts=True,
        )
    ) >= 0

    # C9 with its maximum-cut path and one distance-eight M-edge, followed
    # by a pendant rooted tail.  The quotient inequality is tight here:
    # the M-edge joins the path root to the unique off-path component.
    thin = _path_tail_fixture(
        9,
        [(i, i + 1) for i in range(8)],
        [(0, 8)],
        tail_length=5,
    )
    thin_record = quotient_cut_bound(**thin, reproduce_all_component_cuts=True)
    assert len(thin_record.mixed_m_edges) == 1
    assert thin_record.attachments == 1
    assert set(thin_record.per_cut_margins) == {0}
    assert min(all_path_subset_margins(**thin, reproduce_all_component_cuts=True)) >= 0


def test_mixed_series_fixture_exact_average() -> None:
    fixture = mixed_distance_composite()
    path = canonical_geodesic(
        int(fixture["n"]),
        fixture["edges"],
        int(fixture["w"]),
        int(fixture["x0"]),
    )
    record = quotient_cut_bound(
        n=int(fixture["n"]),
        b_edges=fixture["edges"],
        m_edges=fixture["M"],
        path=path,
        reproduce_all_component_cuts=True,
    )
    assert record.s == 5
    assert record.attachments <= 2 * record.s


def test_forced_hub_and_path_packing_kills_have_no_valid_stub() -> None:
    # These mandatory unrooted counterexamples cannot falsify a theorem
    # whose hypothesis includes a one-stub RFC: every possible nontrivial
    # stub pair violates RFC.  This is checked exactly over all cuts by the
    # zero-slack characterization used in valid_stub_pairs.
    for graph6, cut in (("G?`F`w", 15), ("K??E@_qi?]Ia", 63)):
        fixture = colored_fixture(graph6, cut)
        n = fixture.n
        bit = xor_bits(n)
        slack = np.zeros(1 << n, dtype=np.int32)
        for u, v in fixture.b_edges:
            slack += bit[u] ^ bit[v]
        for u, v in fixture.m_edges:
            slack -= bit[u] ^ bit[v]
        valid = valid_stub_pairs(n, slack)
        assert not valid.any()


def audit_complete_nine_vertex_two_edge_corpus() -> dict[str, int]:
    """Exact audit over every valid rooted |M|=2 instance through n=9.

    The theorem is valid for every geodesic.  The corpus check takes the
    deterministic canonical geodesic for every valid root/stub pair; its
    role is independent falsification, not a proof dependency.
    """

    rooted_instances = inequalities = 0
    for n in range(5, 10):
        bit = xor_bits(n)
        for graph6 in gen_bipartite(n):
            nn, b_edges = parse_graph6(graph6)
            assert nn == n
            distances = all_dists(n, b_edges)
            candidates = m_candidates(n, distances)
            supply = np.zeros(1 << n, dtype=np.int32)
            for u, v in b_edges:
                supply += bit[u] ^ bit[v]
            edge_cuts = {edge: bit[edge[0]] ^ bit[edge[1]] for edge in candidates}
            for m_edges in combinations(candidates, 2):
                if not union_triangle_free(n, b_edges, m_edges):
                    continue
                slack = supply.copy()
                for edge in m_edges:
                    slack -= edge_cuts[edge]
                if slack.min() < 0:
                    continue
                valid = valid_stub_pairs(n, slack)
                for root in range(n):
                    for stub in range(n):
                        if not valid[root][stub]:
                            continue
                        rooted_instances += 1
                        path = canonical_geodesic(n, b_edges, root, stub)
                        record = quotient_cut_bound(
                            n=n,
                            b_edges=b_edges,
                            m_edges=m_edges,
                            path=path,
                            check_rfc=False,
                        )
                        inequalities += len(record.per_cut_margins)
    return {"rooted_instances": rooted_instances, "inequalities": inequalities}


def test_complete_nine_vertex_two_edge_corpus() -> None:
    counts = audit_complete_nine_vertex_two_edge_corpus()
    assert counts["rooted_instances"] > 0
    assert counts["inequalities"] >= counts["rooted_instances"]
