from compute23.gate3.gap_gb_joint_verify import colored_fixture, rooted_metrics

from compute23.gate3.agent_aggregation.private_path_completion import (
    build_private_path_completion,
)
from compute23.gate3.gap_gb_joint_verify import build_long_tail_c5_fixture
from compute23.gate3.gap_gb_series_verify import mixed_distance_composite


def test_long_thin_odd_cycle_is_order_tight() -> None:
    completion = build_private_path_completion(
        ambient_n=9,
        ambient_b_edges=[(i, i + 1) for i in range(8)],
        m_edges=[(0, 8)],
    )
    assert completion.endpoint_count == 2
    assert completion.input_distances == (8,)
    assert completion.order == 9
    assert completion.minimum_cut_slack == 0


def test_mixed_series_fixture_is_strict_and_below_rl_budget() -> None:
    fixture = mixed_distance_composite()
    completion = build_private_path_completion(
        ambient_n=int(fixture["n"]),
        ambient_b_edges=fixture["edges"],
        m_edges=fixture["M"],
    )
    assert sorted(completion.input_distances) == [4, 6]
    assert completion.endpoint_count == 4
    assert completion.order == 12 < int(fixture["n"])
    metrics = rooted_metrics(
        n=int(fixture["n"]),
        b_edges=fixture["edges"],
        m_edges=fixture["M"],
        root=int(fixture["w"]),
        stub=int(fixture["x0"]),
    )
    assert completion.order**2 == 144 <= metrics.rl_budget == 155


def test_mandatory_kills_land_in_dense_completion_complement() -> None:
    for graph6, cut in (("G?`F`w", 15), ("K??E@_qi?]Ia", 63)):
        fixture = colored_fixture(graph6, cut)
        completion = build_private_path_completion(
            ambient_n=fixture.n,
            ambient_b_edges=fixture.b_edges,
            m_edges=fixture.m_edges,
        )
        assert completion.order > fixture.n
        assert completion.input_distances == fixture.m_distances


def test_short_fat_equality_family_is_deliberately_expensive() -> None:
    fixture = build_long_tail_c5_fixture(q=2, tail_length=1)
    completion = build_private_path_completion(
        ambient_n=int(fixture["n"]),
        ambient_b_edges=fixture["b_edges"],
        m_edges=fixture["m_edges"],
    )
    assert completion.input_distances == (4, 4, 4, 4)
    assert completion.endpoint_count == 4
    assert completion.order == 16 > int(fixture["n"])
