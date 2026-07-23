from compute23.gate3.agent_aggregation.distance_four_completion import (
    build_distance_four_completion,
    minimum_proper_edge_coloring,
)


def complete_bipartite(left: range, right: range):
    return tuple((u, v) for u in left for v in right)


def test_balanced_c5_blowup_demand_graph_is_self_tight() -> None:
    # Its distance-four demand graph is K_{q,q}; the q-edge-coloring gives
    # order 2(2q)+q=5q, exactly the ambient C5[q] order.
    q = 2
    demands = complete_bipartite(range(q), range(q, 2 * q))
    completion = build_distance_four_completion(m_edges=demands)
    assert completion.color_count == q
    assert completion.order == 5 * q
    assert completion.completion_distances == (4,) * (q * q)
    assert completion.minimum_cut_slack == 0


def test_odd_cycle_demand_graph_uses_three_colors() -> None:
    demands = tuple((i, (i + 1) % 5) for i in range(5))
    colors = minimum_proper_edge_coloring(demands)
    completion = build_distance_four_completion(m_edges=demands, colors=colors)
    assert completion.color_count == 3
    assert completion.order == 13
    assert completion.completion_distances == (4,) * 5
    assert completion.minimum_cut_slack == 0


def test_disconnected_matching_reuses_one_center_and_stays_valid() -> None:
    demands = ((0, 1), (2, 3), (4, 5))
    completion = build_distance_four_completion(m_edges=demands)
    assert completion.color_count == 1
    assert completion.order == 13
    assert completion.completion_distances == (4, 4, 4)
    assert completion.minimum_cut_slack == 0


def test_triangle_free_shared_neighbor_fixture_has_no_demand_shortcut() -> None:
    # Leaves 0 and 2 acquire a two-edge supply path through port(1), but they
    # are not a demand pair.  Each actual demand remains at distance four.
    demands = ((0, 1), (1, 2), (1, 3))
    completion = build_distance_four_completion(m_edges=demands)
    assert completion.color_count == 3
    assert completion.order == 11
    assert completion.completion_distances == (4, 4, 4)
    assert completion.minimum_cut_slack == 0
