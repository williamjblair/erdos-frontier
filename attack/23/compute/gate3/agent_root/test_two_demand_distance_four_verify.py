from compute23.gate3.agent_root.two_demand_distance_four_verify import verify


def test_two_demand_distance_four_exact_grid() -> None:
    result = verify()
    assert result["verdict"] == "PASS"
    assert result["residual_rows"] > 0
    assert result["dominated_integral_B_values"] > result["residual_rows"]
    assert result["least_margin"] >= 0
