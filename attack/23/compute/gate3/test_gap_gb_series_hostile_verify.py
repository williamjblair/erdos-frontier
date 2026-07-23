"""Independent hostile gate for the G-B series reduction."""

import pathlib
import sys
import unittest


HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from gap_gb_series_hostile_verify import hostile_audit  # noqa: E402


class HostileSeriesAuditTests(unittest.TestCase):
    def test_independent_audit(self):
        result = hostile_audit()
        self.assertEqual(result["verdict"], "PASS")
        self.assertEqual(result["terminal_assignments"], 16)
        self.assertEqual(result["fixture_cuts"], 1 << 14)
        self.assertEqual(result["fixture_tuple"], (14, 2, 9, 4, 50, 104))
        self.assertEqual(result["bridge_component_sizes"], (7, 7))
        self.assertEqual(result["mixed_fixture_tuple"], (17, 2, 11, 5, 74, 155))
        self.assertEqual(result["mixed_distances"], (4, 6))
        self.assertGreater(result["arithmetic_cases"], 5_000_000)
        self.assertEqual(result["minimum_margin"], 0)


if __name__ == "__main__":
    unittest.main()
