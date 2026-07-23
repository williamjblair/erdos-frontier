from compute23.gate3.agent_aggregation.distance_multiset_completion import (
    build_distance_multiset_completion,
    multiset_completion_order,
)
from compute23.gate2.common import parse_graph6
from compute23.gate3.rl_lib import check_rfc_direct, rl_rhs


def test_long_thin_singleton_is_self_tight() -> None:
    completion = build_distance_multiset_completion((8,))
    assert completion.order == 9
    assert completion.completion_distances == (8,)
    assert completion.minimum_cut_slack == 0


def test_short_fat_square_multiplicity_is_self_tight() -> None:
    completion = build_distance_multiset_completion((4,) * 4)
    assert completion.order == 10
    assert completion.completion_distances == (4,) * 4
    assert completion.minimum_cut_slack == 0


def test_mixed_fixture_saves_one_vertex_by_articulation_sum() -> None:
    completion = build_distance_multiset_completion((4, 6))
    assert completion.block_orders == (5, 7)
    assert completion.order == 11
    assert completion.order == 1 + (5 - 1) + (7 - 1)
    assert completion.completion_distances == (4, 6)
    assert completion.minimum_cut_slack == 0


def test_repeated_nonsquare_multiplicity_uses_ceiling_root() -> None:
    assert multiset_completion_order((4, 4, 4)) == 10
    completion = build_distance_multiset_completion((4, 4, 4))
    assert completion.order == 10
    assert len(completion.m_edges) == 3
    assert completion.completion_distances == (4, 4, 4)
    assert completion.minimum_cut_slack == 0


def test_nine_vertex_rooted_double_d4_falsifies_unrestricted_size_gate() -> None:
    # Exact stored signature from logs_enum_n9_m2.txt.  It is rooted-valid and
    # satisfies RL with large slack, but the multiset completion has order ten
    # and its square misses the budget 96.  The gate is therefore not a
    # universal consequence of RFC before the n>=14/BF residual reductions.
    n, b_edges = parse_graph6("H???Fre")
    m_edges = ((3, 5), (4, 6))
    assert n == 9
    assert check_rfc_direct(n, b_edges, m_edges, 0, 1) == (True, None)
    assert rl_rhs(n, 2) == 96
    assert multiset_completion_order((4, 4)) == 10
    assert multiset_completion_order((4, 4)) ** 2 > rl_rhs(n, 2)
