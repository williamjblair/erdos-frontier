"""Exact bounded falsification check for the two-demand distance-four slice.

For each admissible ``(s,d)`` below the configured bound, the quadratic
cost is increasing in ``B``.  It is therefore exact to test the largest
integer ``B`` allowed by ``4*B <= 2*s+d``; every smaller legal ``B`` is
automatically dominated.  This is discovery/audit support, not the
all-natural-number proof, which is in Lean.
"""

from __future__ import annotations

import json


def partner_distance(d: int) -> int:
    if d == 1:
        return 3
    return 2 if d % 2 == 0 else 1


def rl_budget(s: int, d: int) -> int:
    return s * (2 * d + 2 + s) + 2 * s * partner_distance(d)


def verify(limit: int = 1000) -> dict[str, int | str]:
    rows = 0
    dominated_integral_values = 0
    least_margin: int | None = None
    for s in range(5, limit):
        for d in range(3, 2 * s):
            p = partner_distance(d)
            if s + d < 13 or 2 * s * p >= (d + 1) ** 2:
                continue
            b_max = (2 * s + d) // 4
            if b_max < 2:
                continue
            rows += 1
            dominated_integral_values += b_max - 1
            margin = rl_budget(s, d) - (25 + (2 * b_max + 1) ** 2)
            if margin < 0:
                raise AssertionError((s, d, p, b_max, margin))
            least_margin = margin if least_margin is None else min(least_margin, margin)
    return {
        "limit_exclusive": limit,
        "residual_rows": rows,
        "dominated_integral_B_values": dominated_integral_values,
        "least_margin": -1 if least_margin is None else least_margin,
        "verdict": "PASS",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, separators=(",", ":")))
