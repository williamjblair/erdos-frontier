"""Regression gate for the exact one-defect canonical-geometry checker."""

from one_defect_geometry_verify import run_audit


def test_all_canonical_one_defect_geometries() -> None:
    summary = run_audit()
    assert summary.verdict == "PASS"
    assert summary.s_values == (5, 6, 7, 8)
    assert summary.mass_cases == 88
    assert summary.overlap_cases == 22
    assert summary.geometry_cases == 110
    assert summary.legal_pairs == 6910
    assert summary.cut_feasible_sets_at_least_two == 83000
    assert summary.largest_cut_size == 2
    assert summary.least_pair_margin == 0
    assert summary.least_set_budget_margin == 60
