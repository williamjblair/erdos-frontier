from compute23.gate3.agent_root.isometric_cut_basis_verify import verify


def test_isometric_cut_basis_exact_grid() -> None:
    result = verify()
    assert result["verdict"] == "PASS"
    assert result["rows"] > 0
    assert result["least_margin"] >= 0
