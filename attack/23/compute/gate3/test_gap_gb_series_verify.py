"""Hostile exact tests for the Erdős #23 G-B series reduction."""

import itertools
import pathlib
import sys
import unittest


HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from gap_gb_series_verify import (  # noqa: E402
    boundary_composite,
    cut_count,
    partner_distance,
    rl_budget,
    separation,
    series_budget_margin,
    verify_boundary_composite,
    verify_mixed_distance_composite,
)
from rl_lib import all_dists, check_rfc_direct, gamma_of, union_triangle_free  # noqa: E402


class SeriesArithmeticTests(unittest.TestCase):
    def test_partner_distance_exact_surface(self):
        self.assertEqual(
            [partner_distance(d) for d in range(1, 11)],
            [3, 2, 1, 2, 1, 2, 1, 2, 1, 2],
        )

    def test_four_terminal_separation_triangle(self):
        for w1, x1, w2, x2 in itertools.product((0, 1), repeat=4):
            self.assertLessEqual(
                separation(w1, x2),
                separation(w1, x1)
                + separation(x1, w2)
                + separation(w2, x2),
            )

    def test_budget_superadditivity_exhaustive_box(self):
        # Includes zero-slack sides, all parity transitions, and dimensions
        # well beyond the n=14 frontier boundary.
        for d1 in range(1, 65):
            for d2 in range(1, 65):
                for s1 in range(0, 17):
                    for s2 in range(0, 17):
                        margin = series_budget_margin(s1, d1, s2, d2)
                        self.assertGreaterEqual(margin, 0)
                        self.assertEqual(
                            margin,
                            rl_budget(s1 + s2, d1 + d2 + 1)
                            - rl_budget(s1, d1)
                            - rl_budget(s2, d2),
                        )

    def test_induction_sizes_when_both_sides_have_four_vertices(self):
        for d1 in range(1, 65):
            for d2 in range(1, 65):
                for n1 in range(4, 20):
                    for n2 in range(4, 20):
                        n = n1 + n2
                        self.assertLess(n1 + partner_distance(d1), n)
                        self.assertLess(n2 + partner_distance(d2), n)


class SeriesBoundaryFixtureTests(unittest.TestCase):
    def test_n14_two_edge_middle_regime_fixture(self):
        fixture = boundary_composite()
        n = fixture["n"]
        edges = fixture["edges"]
        M = fixture["M"]
        w = fixture["w"]
        x0 = fixture["x0"]
        dist = all_dists(n, edges)
        d = dist[w][x0]
        s = n - 1 - d
        gamma = gamma_of(M, dist)

        self.assertEqual((n, len(M), d, s, gamma), (14, 2, 9, 4, 50))
        self.assertTrue(union_triangle_free(n, edges, M))
        self.assertEqual(check_rfc_direct(n, edges, M, w, x0), (True, None))
        self.assertLess(2 * s * partner_distance(d), (d + 1) ** 2)
        self.assertLessEqual(gamma, rl_budget(s, d))
        self.assertEqual(rl_budget(s, d), 104)

    def test_bridge_is_a_genuine_cut_and_cut_counts_decompose(self):
        fixture = boundary_composite()
        n = fixture["n"]
        edges = fixture["edges"]
        M = fixture["M"]
        bridge = fixture["bridge"]
        left = fixture["left_vertices"]
        right = fixture["right_vertices"]
        edges1 = fixture["edges1"]
        edges2 = fixture["edges2"]
        M1 = fixture["M1"]
        M2 = fixture["M2"]

        self.assertEqual(set(left) | set(right), set(range(n)))
        self.assertFalse(set(left) & set(right))
        self.assertNotIn(bridge, edges1)
        self.assertNotIn(bridge, edges2)

        for T in range(1 << n):
            bridge_crosses = separation((T >> bridge[0]) & 1, (T >> bridge[1]) & 1)
            self.assertEqual(
                cut_count(edges, T),
                cut_count(edges1, T) + cut_count(edges2, T) + bridge_crosses,
            )
            self.assertEqual(cut_count(M, T), cut_count(M1, T) + cut_count(M2, T))

    def test_full_boundary_audit_summary(self):
        summary = verify_boundary_composite()
        self.assertEqual(summary["rfc_min_slack"], 0)
        self.assertEqual(summary["series_budget_margin"], 40)
        self.assertEqual(summary["global_rl_slack"], 54)
        self.assertEqual(summary["cuts_checked"], 1 << 14)

    def test_mixed_even_distance_fixture(self):
        summary = verify_mixed_distance_composite()
        self.assertEqual(summary["tuple"], (17, 2, 11, 5, 74, 155))
        self.assertEqual(summary["M_distances"], (4, 6))
        self.assertEqual(summary["component_sizes"], (7, 10))
        self.assertEqual(summary["series_budget_margin"], 60)
        self.assertEqual(summary["global_rl_slack"], 81)


if __name__ == "__main__":
    unittest.main()
