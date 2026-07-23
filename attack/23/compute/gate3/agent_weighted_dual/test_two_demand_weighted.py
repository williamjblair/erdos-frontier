"""Exact hostile checks for the weighted two-demand RL closure."""

from __future__ import annotations

import numpy as np

from compute23.gate3.agent_weighted_dual.joint_distance_counterexample import (
    build_counterexample,
)
from compute23.gate3.gap_gb_joint_verify import colored_fixture
from compute23.gate3.rl_lib import valid_stub_pairs, xor_bits


def partner_distance(d: int) -> int:
    if d == 1:
        return 3
    return 2 if d % 2 == 0 else 1


def test_weighted_arithmetic_complete_box() -> None:
    checked = 0
    for s in range(1, 81):
        for d in range(1, 81):
            if not 2 * d < s:
                continue
            p = partner_distance(d)
            budget = s * (2 * d + 2 + s) + 2 * s * p
            for smaller in range(0, 2 * (s + d) + 1):
                for larger in range(smaller, (2 * s + d) // 2 + 1):
                    if smaller + 2 * larger > 2 * (s + d):
                        continue
                    checked += 1
                    assert (smaller + 1) ** 2 + (larger + 1) ** 2 <= budget
    assert checked == 2_702_789


def test_partner_two_arithmetic_includes_closed_boundary() -> None:
    checked = 0
    boundary_checked = 0
    for s in range(1, 81):
        for d in range(1, 81):
            if not 2 * d <= s:
                continue
            p = 2
            budget = s * (2 * d + 2 + s) + 2 * s * p
            for smaller in range(0, 2 * (s + d) + 1):
                for larger in range(smaller, (2 * s + d) // 2 + 1):
                    if smaller + 2 * larger > 2 * (s + d):
                        continue
                    checked += 1
                    boundary_checked += 2 * d == s
                    assert (smaller + 1) ** 2 + (larger + 1) ** 2 <= budget
    assert checked == 2_765_969
    assert boundary_checked == 63_180


def test_partner_two_first_three_rows_below_boundary() -> None:
    checked = 0
    by_defect = {defect: 0 for defect in range(4)}
    for d in range(6, 81):
        for defect in range(4):
            s = 2 * d - defect
            p = 2
            budget = s * (2 * d + 2 + s) + 2 * s * p
            for smaller in range(0, 2 * (s + d) + 1):
                for larger in range(smaller, (2 * s + d) // 2 + 1):
                    if smaller + 2 * larger > 2 * (s + d):
                        continue
                    checked += 1
                    by_defect[defect] += 1
                    assert (smaller + 1) ** 2 + (larger + 1) ** 2 <= budget
    assert checked == 1_909_006
    assert by_defect == {0: 486_964, 1: 480_439, 2: 473_989, 3: 467_614}


def test_equal_strictness_closes_only_the_claimed_near_rows() -> None:
    checked = 0
    for d in range(3, 81):
        p = partner_distance(d)
        max_defect = 6 if p == 2 else 3
        for defect in range(max_defect + 1):
            s = 2 * d - defect
            if s < 5 or s + d < 12 or 2 * s * p >= (d + 1) ** 2:
                continue
            budget = s * (2 * d + 2 + s) + 2 * s * p
            for smaller in range(6, (2 * s + d) // 2 + 1, 2):
                for larger in range(smaller, (2 * s + d) // 2 + 1, 2):
                    if smaller + 2 * larger > 2 * (s + d):
                        continue
                    if (
                        smaller == larger
                        and 3 * smaller > 2 * (s + d - 1)
                    ):
                        continue
                    checked += 1
                    assert (smaller + 1) ** 2 + (larger + 1) ** 2 <= budget
    assert checked == 597_493

    # These are the first unequal profiles beyond the claimed uniform rows.
    for s, d, smaller, larger, deficit in (
        (10, 7, 10, 12, 10),
        (9, 8, 10, 12, 11),
    ):
        p = partner_distance(d)
        assert 2 * larger <= 2 * s + d
        assert smaller + 2 * larger <= 2 * (s + d)
        assert smaller != larger
        budget = s * (2 * d + 2 + s) + 2 * s * p
        assert (smaller + 1) ** 2 + (larger + 1) ** 2 - budget == deficit


def test_n76_false_sum_bound_is_closed_by_weighted_bounds() -> None:
    record = build_counterexample()
    smaller, larger = record["demand_distances"]
    s, d = record["s"], record["d"]
    assert record["distance_sum"] > record["joint_rhs"]
    assert 2 * d < s
    assert 2 * larger <= 2 * s + d
    assert smaller + 2 * larger <= 2 * (s + d)
    assert record["total_cost"] <= record["rl_budget"]


def _valid_root_count(graph6: str, cut: int) -> tuple[int, int, tuple[int, ...]]:
    fixture = colored_fixture(graph6, cut)
    bits = xor_bits(fixture.n)
    slack = np.zeros(1 << fixture.n, dtype=np.int16)
    for u, v in fixture.b_edges:
        slack += bits[u] ^ bits[v]
    for u, v in fixture.m_edges:
        slack -= bits[u] ^ bits[v]
    roots = valid_stub_pairs(fixture.n, slack)
    return int(roots.sum()), len(fixture.m_edges), fixture.m_distances


def test_mandatory_old_falsifiers_are_not_silently_used() -> None:
    # Forced hub: exactly two distance-four demands, but no rooted stub pair.
    assert _valid_root_count("G?`F`w", 15) == (0, 2, (4, 4))
    # Path-packing witness: four demands and no rooted stub pair.
    assert _valid_root_count("K??E@_qi?]Ia", 63) == (0, 4, (4, 4, 4, 4))
    # Mixed-distance Holder witness: two demands and no rooted stub pair.
    assert _valid_root_count("H?AFBo]", 31) == (0, 2, (4, 6))
