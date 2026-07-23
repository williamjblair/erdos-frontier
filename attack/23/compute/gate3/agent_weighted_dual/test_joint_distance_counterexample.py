"""Regression tests for the all-nonbridge GB-2SUM counterexample."""

from __future__ import annotations

from compute23.gate3.agent_weighted_dual.joint_distance_counterexample import (
    BASE_DEMANDS,
    BASE_EDGES,
    BASE_N,
    BASE_ROOT,
    BASE_STUB,
    build_counterexample,
    cut_count,
    exact_base_rfc,
    exact_local_truth_tables,
    sep,
)


def test_base_symmetric_rfc_is_exhaustive() -> None:
    minimum = 10**9
    zero_slack_cuts = 0
    for mask in range(1 << BASE_N):
        supply = cut_count(BASE_EDGES, mask)
        demand = cut_count(BASE_DEMANDS, mask)
        rooted = sep((mask >> BASE_ROOT) & 1, (mask >> BASE_STUB) & 1)
        slack = supply - demand - rooted
        assert slack >= 0
        minimum = min(minimum, slack)
        zero_slack_cuts += slack == 0
    assert minimum == exact_base_rfc() == 0
    assert zero_slack_cuts == 24


def test_gadget_cut_inequalities_are_complete_truth_tables() -> None:
    assert exact_local_truth_tables() == {
        "endpoint_move": 16,
        "root_move": 8,
        "diamond": 16,
    }


def test_strict_residual_all_nonbridge_joint_bound_failure() -> None:
    record = build_counterexample(diamond_blocks=16, root_half_cycle=9)
    assert record["n"] == 76
    assert record["edge_count"] == 96
    assert (record["d"], record["s"], record["p"]) == (11, 64, 1)
    assert record["demand_distances"] == (38, 38)
    assert record["distance_sum"] == 76
    assert record["joint_rhs"] == 75
    assert record["joint_excess"] == 1
    assert record["strict_pair"] == (128, 144)
    assert record["root_geodesic_bridge_flags"] == (False,) * 11

    # This fixture kills only the proposed linear sufficient condition.
    # It is deliberately asserted not to be a counterexample to RL.
    assert record["total_cost"] == 3042
    assert record["rl_budget"] == 5760
    assert record["total_cost"] <= record["rl_budget"]
