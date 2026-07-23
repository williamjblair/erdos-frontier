"""Regression test for the exact defect-two structural enumerator."""

from two_defect_geometry_verify import run


def test_two_defect_geometries() -> None:
    summary = run()
    assert summary.verdict == "PASS"
    assert summary.s_values == (4, 5, 6, 7, 8)
    assert summary.geometry_cases == 1505
    assert summary.legal_pairs == 85145
    assert summary.aligned_pairs == 84570
    assert summary.unaligned_pairs == 535
    assert summary.outside_pairs == 40
    assert summary.fully_aligned_cases == 1200
    assert summary.nonaligned_by_shape == (
        ("mass_overlap", 80),
        ("mass_q3", 140),
        ("mass_span", 40),
        ("pure_span", 45),
    )
    assert summary.largest_adjacent_extra == 2
    assert summary.largest_capacity_excess == 2
