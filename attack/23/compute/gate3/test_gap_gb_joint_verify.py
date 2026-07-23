from compute23.gate3.gap_gb_joint_verify import (
    build_long_tail_c5_fixture,
    colored_fixture,
    double_slack_resource_certificate,
    endpoint_gamma_block_absorbs,
    endpoint_move_budget_nonincrease,
    exact_series_induction_gate,
    joint_distance_excess,
    residual_regime,
    residual_series_dispatch,
    rooted_metrics,
    threshold_separation_sum,
)


def test_residual_regime_is_strict_and_keeps_all_boundaries() -> None:
    assert residual_regime(n=14, d=9, m_count=2)
    assert not residual_regime(n=13, d=9, m_count=2)
    assert not residual_regime(n=14, d=2, m_count=2)
    assert not residual_regime(n=14, d=9, m_count=1)


def test_c5_three_long_tail_kills_uncorrected_joint_distance_bound() -> None:
    fixture = build_long_tail_c5_fixture(q=3, tail_length=5)
    metrics = rooted_metrics(**fixture)
    assert metrics.rfc_valid
    assert metrics.n == 20
    assert metrics.d == 5
    assert metrics.s == 14
    assert metrics.m_distances == (4,) * 9
    assert metrics.gamma == 225
    assert residual_regime(metrics.n, metrics.d, len(metrics.m_distances))
    assert sum(metrics.m_distances) == 36 > 2 * metrics.s
    assert metrics.gamma <= metrics.rl_budget


def test_mandatory_unrooted_kills_reproduce_exactly() -> None:
    double = colored_fixture("G?`F`w", 15)
    assert double.m_distances == (4, 4)
    assert double.gamma == 50
    assert double.forced_hub_load == 10 > double.n

    path = colored_fixture("K??E@_qi?]Ia", 63)
    assert path.m_distances == (4, 4, 4, 4)
    assert sum(d + 1 for d in path.m_distances) == 20 > len(path.all_edges)
    assert sum(path.m_distances) == 16 > len(path.b_edges)


def test_two_edge_mixed_fixture_and_joint_excess() -> None:
    metrics = rooted_metrics(
        n=10,
        b_edges=((0, 7), (1, 7), (2, 7), (3, 8), (4, 8), (5, 8),
                 (0, 9), (1, 9), (3, 9), (4, 9), (6, 9)),
        m_edges=((2, 5), (7, 8)),
        root=6,
        stub=9,
    )
    assert metrics.rfc_valid
    assert metrics.m_distances == (4, 6)
    assert metrics.d == 1 and metrics.s == 8
    assert joint_distance_excess(metrics.m_distances) == 2
    assert sum(metrics.m_distances) <= 2 * metrics.s


def test_exact_series_induction_gate_strictly_extends_four_by_four() -> None:
    assert exact_series_induction_gate(n1=2, n2=9, d1=1, d2=5)
    assert exact_series_induction_gate(n1=3, n2=9, d1=2, d2=4)
    assert not exact_series_induction_gate(n1=2, n2=9, d1=1, d2=4)
    assert exact_series_induction_gate(n1=4, n2=4, d1=1, d2=1)


def test_residual_series_dispatch_exhaustive_bounded_reproduction() -> None:
    counts = {"induction": 0, "endpoint_pair": 0}
    for n1 in range(2, 40):
        for n2 in range(2, 40):
            for d1 in range(1, n1):
                for d2 in range(1, n2):
                    n = n1 + n2
                    d = d1 + d2 + 1
                    if not residual_regime(n, d, m_count=2):
                        continue
                    outcome = residual_series_dispatch(
                        n1=n1, n2=n2, d1=d1, d2=d2
                    )
                    counts[outcome] += 1
                    if outcome == "endpoint_pair":
                        assert n1 == 2 or n2 == 2
    assert counts["induction"] > 0
    assert counts["endpoint_pair"] > 0


def test_endpoint_move_budget_nonincrease_exact_grid() -> None:
    assert all(
        endpoint_move_budget_nonincrease(s=s, d=d)
        for s in range(0, 100)
        for d in range(2, 100)
    )


def test_endpoint_gamma_block_absorption_exact_grid() -> None:
    assert all(
        endpoint_gamma_block_absorbs(order=order, s=s, d=d)
        for order in range(2, 100)
        for s in range(0, 100)
        for d in range(1, 100)
    )


def test_threshold_layer_cake_identity_exact_grid() -> None:
    for height in range(0, 100):
        for a in range(height + 1):
            for b in range(height + 1):
                assert threshold_separation_sum(a, b, height) == abs(a - b)


def test_double_slack_resource_certificate_exact_compositions() -> None:
    def compositions(total: int, parts: int):
        if parts == 1:
            yield (total,)
            return
        for first in range(1, total - parts + 2):
            for tail in compositions(total - first, parts - 1):
                yield (first,) + tail

    for s in range(5, 14):
        for total in range(1, s):
            for parts in range(1, total + 1):
                for resources in compositions(total, parts):
                    distances = tuple(2 * r + 2 for r in resources)
                    assert double_slack_resource_certificate(
                        s=s, distances=distances, resources=resources
                    )
