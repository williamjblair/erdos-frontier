#!/usr/bin/env python3
"""Independent exact-arithmetic audit of the two-demand RL landings.

This is deliberately not a proof substitute: the unbounded argument is the Lean
kernel proof.  The script reproduces the integer residue table, the exact
fractional witnesses that defeat the discarded continuous proof, and an
exhaustive integer check through a configurable slack bound.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction


def partner_distance(distance: int) -> int:
    if distance == 1:
        return 3
    return 2 if distance % 2 == 0 else 1


def rl_budget(slack: int, distance: int) -> int:
    partner = partner_distance(distance)
    return slack * (2 * distance + 2 + slack) + 2 * slack * partner


def is_residual(slack: int, distance: int) -> bool:
    partner = partner_distance(distance)
    return (
        slack >= 5
        and slack + distance >= 13
        and distance >= 3
        and distance < 2 * slack
        and 2 * slack * partner < (distance + 1) ** 2
    )


@dataclass(frozen=True)
class ResidueRow:
    slack_mod_two: int
    distance_mod_four: int
    partner: int
    x_offset: int
    y_offset: int
    m_offset: int
    minimum_gap: int

    def corner(self, slack: int, distance: int) -> tuple[int, int, int]:
        return (
            distance + self.x_offset,
            2 * slack + distance + self.y_offset,
            slack + distance + self.m_offset,
        )


# X, Y, M are the scaled convex corner used by the Lean proof.  The two rows
# with Y offset zero and odd distance intentionally use a one-unit relaxation
# of the sharp B cap; this removes natural subtraction without weakening the
# final budget inequality.
RESIDUE_ROWS = (
    ResidueRow(0, 0, 2, 2, 2, 2, 4),
    ResidueRow(0, 1, 1, 1, 1, 1, 3),
    ResidueRow(0, 2, 2, 4, 0, 2, 2),
    ResidueRow(0, 3, 1, 2, 0, 1, 1),
    ResidueRow(1, 0, 2, 6, 0, 3, 2),
    ResidueRow(1, 1, 1, 4, 0, 2, 1),
    ResidueRow(1, 2, 2, 4, 2, 3, 4),
    ResidueRow(1, 3, 1, 3, 1, 2, 3),
)

ROW_BY_RESIDUE = {
    (row.slack_mod_two, row.distance_mod_four): row for row in RESIDUE_ROWS
}


def check_fractional_counterexamples() -> tuple[Fraction, Fraction]:
    slack, distance = 5, 9
    partner = partner_distance(distance)
    budget = Fraction(rl_budget(slack, distance))

    b = Fraction(19, 4)
    assert 4 * b == 2 * slack + distance
    one_four_cost = Fraction(25) + (2 * b + 1) ** 2
    assert one_four_cost == Fraction(541, 4)
    assert budget == 135
    assert one_four_cost - budget == Fraction(1, 4)

    a = Fraction(9, 4)
    assert 2 <= a <= b
    assert 2 * a + 2 * b == slack + distance + partner - 1
    pair_cost = (2 * a + 1) ** 2 + (2 * b + 1) ** 2
    assert pair_cost == Fraction(281, 2)
    assert pair_cost - budget == Fraction(11, 2)
    return one_four_cost - budget, pair_cost - budget


def check_residue_table(max_slack: int) -> int:
    checked = 0
    for slack in range(5, max_slack + 1):
        for distance in range(3, 2 * slack):
            if not is_residual(slack, distance):
                continue
            row = ROW_BY_RESIDUE[(slack % 2, distance % 4)]
            assert row.partner == partner_distance(distance)
            assert distance + row.minimum_gap <= 2 * slack
            x_corner, y_corner, mass_corner = row.corner(slack, distance)
            assert x_corner + y_corner == 2 * mass_corner
            assert x_corner**2 + y_corner**2 <= 4 * rl_budget(slack, distance)
            checked += 1
    return checked


def check_integer_landings(max_slack: int) -> tuple[int, int, int]:
    """Check all B values and the maximal admissible A for each B.

    For fixed B the pair cost is strictly increasing in A, so checking the
    maximal admissible A verifies every smaller admissible A.  `pair_instances`
    counts all such A values, not merely the maxima evaluated by the loop.
    """

    frontiers = 0
    one_four_instances = 0
    pair_instances = 0
    for slack in range(5, max_slack + 1):
        for distance in range(3, 2 * slack):
            if not is_residual(slack, distance):
                continue
            frontiers += 1
            partner = partner_distance(distance)
            budget = rl_budget(slack, distance)
            b_cap = (2 * slack + distance) // 4

            if b_cap >= 2:
                one_four_instances += b_cap - 1
                assert 25 + (2 * b_cap + 1) ** 2 <= budget

            joint_mass = slack + distance + partner - 1
            for b in range(2, b_cap + 1):
                a_cap = min(b, (joint_mass - 2 * b) // 2)
                if a_cap < 2:
                    continue
                pair_instances += a_cap - 1
                assert 2 * a_cap + 2 * b <= joint_mass
                assert (2 * a_cap + 1) ** 2 + (2 * b + 1) ** 2 <= budget

    return frontiers, one_four_instances, pair_instances


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-slack", type=int, default=400)
    args = parser.parse_args()
    if args.max_slack < 5:
        parser.error("--max-slack must be at least 5")

    one_excess, pair_excess = check_fractional_counterexamples()
    residue_frontiers = check_residue_table(args.max_slack)
    frontiers, one_instances, pair_instances = check_integer_landings(args.max_slack)
    assert residue_frontiers == frontiers

    print(f"fractional one-four excess: {one_excess}")
    print(f"fractional pair excess: {pair_excess}")
    print(f"residual frontiers checked: {frontiers}")
    print(f"integer one-four instances covered: {one_instances}")
    print(f"integer pair instances covered: {pair_instances}")
    print("PASS: residue table and integer landings reproduced exactly")


if __name__ == "__main__":
    main()
