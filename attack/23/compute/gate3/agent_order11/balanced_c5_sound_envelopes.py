#!/usr/bin/env python3
"""Exact chosen-colouring landings for sound balanced-C5 profile envelopes.

Input caches must be orbit-invariant or Aut(R)-averaged.  A floating local
MaxCut search chooses each colouring, but the reported landing is then
recomputed with integer multinomial weights and ``Fraction`` arithmetic.
Finding a landing at most 2/25 is sufficient at the sharp C5 boundary; no
claim of MaxCut optimality is needed.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

from order11_k8_lift import canonicalize, decode_g6, encode_g6, local_maxcut


def compositions(total: int, parts: int, prefix=()):
    if parts == 1:
        yield prefix + (total,)
        return
    for first in range(total + 1):
        yield from compositions(total - first, parts - 1, prefix + (first,))


def blowup(composition: tuple[int, ...]) -> list[int]:
    part = []
    for i, size in enumerate(composition):
        part.extend([i] * size)
    adjacency = [0] * len(part)
    for a in range(len(part)):
        for b in range(a + 1, len(part)):
            if (part[a] - part[b]) % 5 in (1, 4):
                adjacency[a] |= 1 << b
                adjacency[b] |= 1 << a
    return adjacency


def c5_state_counts(lines: list[str], n: int) -> np.ndarray:
    canonical_lines = canonicalize(lines)
    row = {key: i for i, key in enumerate(canonical_lines)}
    compositions_list = list(compositions(n, 5))
    graphs = [encode_g6(blowup(c)) for c in compositions_list]
    canonical_graphs = canonicalize(graphs)
    counts = np.zeros(len(lines), dtype=np.int64)
    for composition, key in zip(compositions_list, canonical_graphs):
        multiplicity = math.factorial(n)
        for size in composition:
            multiplicity //= math.factorial(size)
        counts[row[key]] += multiplicity
    if int(counts.sum()) != 5**n:
        raise AssertionError((counts.sum(), 5**n))
    return counts


def evaluate(cache: Path) -> dict[str, object]:
    data = np.load(cache)
    n = int(data["state_order"])
    lines = data["lines"].tolist()
    q_count = c5_state_counts(lines, n)
    entry_j = data["entry_j"].astype(np.int32)
    rid = data["rid"].astype(np.int32)
    pa = data["pa"].astype(np.int32)
    pb = data["pb"].astype(np.int32)
    profile_count = data["profile_count"].astype(np.int32)
    choose_two = math.comb(n, 2)
    if "entry_count" in data:
        kind = "aut-averaged"
        entry_count = data["entry_count"].astype(np.int64)
        aut_size = data["aut_size"].astype(np.int64)
    else:
        kind = "orbit-invariant"
        entry_count = np.ones(len(entry_j), dtype=np.int64)
        aut_size = np.ones(len(profile_count), dtype=np.int64)

    landing = Fraction()
    positive_roots = 0
    max_active = 0
    for root in range(len(profile_count)):
        entries = np.flatnonzero(rid == root)
        positive = q_count[entry_j[entries]] > 0
        entries = entries[positive]
        if len(entries) == 0:
            continue
        positive_roots += 1
        small = np.minimum(pa[entries], pb[entries])
        large = np.maximum(pa[entries], pb[entries])
        size = int(profile_count[root])
        key = small.astype(np.int64) * size + large
        unique, inverse = np.unique(key, return_inverse=True)
        integer_weight = q_count[entry_j[entries]] * entry_count[entries]
        grouped = np.bincount(inverse, weights=integer_weight).round().astype(np.int64)
        left, right = unique // size, unique % size
        active = len(np.unique(np.concatenate([left, right])))
        max_active = max(max_active, active)
        color = local_maxcut(
            size,
            left,
            right,
            grouped.astype(float),
            seed=91_000 + root,
            starts=64,
        )
        same = color[pa[entries]] == color[pb[entries]]
        exact_numerator = int(np.sum(integer_weight[same]))
        landing += Fraction(
            exact_numerator,
            choose_two * 5**n * int(aut_size[root]),
        )
    if landing > Fraction(2, 25):
        verdict = "CHOSEN_COLORING_ABOVE_SHARP_BOUND"
    else:
        verdict = "PASS_AT_OR_BELOW_2_25"
    return {
        "cache": str(cache),
        "kind": kind,
        "state_order": n,
        "root_order": n - 2,
        "positive_root_types": positive_roots,
        "max_active_profiles": max_active,
        "chosen_landing": f"{landing.numerator}/{landing.denominator}",
        "chosen_landing_float": float(landing),
        "gap_from_2_25": f"{(landing-Fraction(2,25)).numerator}/{(landing-Fraction(2,25)).denominator}",
        "verdict": verdict,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("caches", type=Path, nargs="+")
    args = parser.parse_args()
    results = [evaluate(cache) for cache in args.caches]
    print(json.dumps({"results": results}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
