"""Exact-substrate / floating-discovery LP for level-aligned demands.

For BFS layer sizes ``a_0,...,a_d``, every level cut has residual capacity
at most ``a_{r-1} a_r - 1`` after reserving the root--stub demand.  Demand
interval incidence is consecutive-ones; the displayed optima are discovery
data until an integer dual is extracted and checked.
"""

from __future__ import annotations

import sys

from scipy.optimize import linprog

from compute23.gate3.rl_lib import p_of_d


def compositions(total: int, parts: int, prefix: tuple[int, ...] = ()):
    if parts == 1:
        yield prefix + (total,)
        return
    for value in range(total + 1):
        yield from compositions(total - value, parts - 1, prefix + (value,))


def solve(s: int, d: int):
    intervals = [
        (left, right)
        for left in range(d + 1)
        for right in range(left + 4, d + 1, 2)
    ]
    costs = [(right - left + 1) ** 2 for left, right in intervals]
    incidence = [
        [int(left < level <= right) for left, right in intervals]
        for level in range(1, d + 1)
    ]
    best = None
    for extra in compositions(s, d + 1):
        layers = tuple(value + 1 for value in extra)
        capacity = tuple(
            layers[level - 1] * layers[level] - 1
            for level in range(1, d + 1)
        )
        result = linprog(
            [-cost for cost in costs],
            A_ub=incidence + [[-1] * len(intervals)],
            b_ub=list(capacity) + [-2],
            bounds=[(0, None)] * len(intervals),
            method="highs",
        )
        if not result.success:
            continue
        value = -float(result.fun)
        if best is None or value > best[0] + 1e-8:
            best = (
                value,
                layers,
                capacity,
                tuple(
                    (intervals[index], float(weight))
                    for index, weight in enumerate(result.x)
                    if weight > 1e-8
                ),
            )
    budget = s * (2 * d + 2 + s) + 2 * s * p_of_d(d)
    return budget, best


if __name__ == "__main__":
    s, d = map(int, sys.argv[1:3])
    print(s, d, solve(s, d))
