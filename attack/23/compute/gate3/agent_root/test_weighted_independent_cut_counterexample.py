from compute23.gate3.agent_root.weighted_independent_cut_counterexample import (
    certificate,
)


def test_weighted_independent_shortcut_is_false() -> None:
    result = certificate()
    assert result["maximum_independent_degree_sum"] == 9
    assert result["weighted_claim_scaled_lhs"] == 225
    assert result["weighted_claim_scaled_rhs"] == 236


def test_actual_bipartization_bound_survives() -> None:
    result = certificate()
    assert result["maximum_cut"] == 10
    assert result["beta"] == 2
    assert result["erdos23_scaled_lhs"] == 50 < 64
