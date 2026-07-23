"""Exact bounded check of the isometric-cut arithmetic landing.

With at least two even legal distances and total at most ``d``, convexity
puts four units on one demand and every remaining even unit on the other.
The script checks that exact extremizer.  The all-natural proof is in Lean.
"""

from __future__ import annotations

import json


def partner_distance(d: int) -> int:
    if d == 1:
        return 3
    return 2 if d % 2 == 0 else 1


def rl_budget(s: int, d: int) -> int:
    return s * (2 * d + 2 + s) + 2 * s * partner_distance(d)


def verify(limit: int = 1001) -> dict[str, int | str]:
    rows = 0
    least_margin: int | None = None
    for s in range(5, limit):
        for d in range(8, 2 * s + 1):
            even_total = d if d % 2 == 0 else d - 1
            large = even_total - 4
            cost = (large + 1) ** 2 + 25
            margin = rl_budget(s, d) - cost
            if margin < 0:
                raise AssertionError((s, d, large, margin))
            rows += 1
            least_margin = margin if least_margin is None else min(least_margin, margin)
    return {
        "limit_exclusive": limit,
        "rows": rows,
        "least_margin": -1 if least_margin is None else least_margin,
        "verdict": "PASS",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, separators=(",", ":")))
