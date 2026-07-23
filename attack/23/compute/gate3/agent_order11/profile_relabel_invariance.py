#!/usr/bin/env python3
"""Mandatory relabel-invariance gate for finite rooted-profile rows.

The two frozen witnesses first reproduce the failure of choosing one raw
canonical-coordinate tie-breaking.  The second half checks that averaging
the same colouring over Aut(R) restores exact invariance.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
from fractions import Fraction

from order11_k8_lift import _root_catalog, canon_label, decode_g6, geng_lines, induced


WITNESSES = [
    (9, "H?Bedrw", [0, 2, 5, 7, 4, 8, 3, 1, 6], (8, 6, 30)),
    (10, "I??E@bG}?", [3, 7, 9, 8, 4, 6, 5, 2, 0, 1], (10, 12, 24)),
]


def relabel_new_to_old(adjacency: list[int], new_to_old: list[int]) -> list[int]:
    n = len(adjacency)
    output = [0] * n
    for a in range(n):
        for b in range(a + 1, n):
            if (adjacency[new_to_old[a]] >> new_to_old[b]) & 1:
                output[a] |= 1 << b
                output[b] |= 1 << a
    return output


def colour(root_key: tuple[int, ...], profile: tuple[int, ...]) -> int:
    digest = hashlib.sha256(bytes(root_key) + b"\xff" + bytes(profile)).digest()
    return digest[0] & 1


def raw_same_ordered(adjacency: list[int]) -> int:
    n = len(adjacency)
    root_order = n - 2
    same = 0
    for a in range(n):
        for b in range(n):
            if a == b or not ((adjacency[a] >> b) & 1):
                continue
            root_vertices = [v for v in range(n) if v != a and v != b]
            key, inverse = canon_label(root_order, induced(adjacency, root_vertices))
            profile_a = tuple(
                sorted(
                    inverse[p]
                    for p, vertex in enumerate(root_vertices)
                    if (adjacency[a] >> vertex) & 1
                )
            )
            profile_b = tuple(
                sorted(
                    inverse[p]
                    for p, vertex in enumerate(root_vertices)
                    if (adjacency[b] >> vertex) & 1
                )
            )
            same += colour(key, profile_a) == colour(key, profile_b)
    return same


_CATALOG = {}


def aut_averaged_signature(adjacency: list[int]) -> tuple[Fraction, ...]:
    n = len(adjacency)
    root_order = n - 2
    catalog = _CATALOG.get(root_order)
    if catalog is None:
        catalog = _root_catalog(root_order)
        _CATALOG[root_order] = catalog
    keys, automorphisms, _ = catalog
    root_id = {key: i for i, key in enumerate(keys)}
    result = [Fraction() for _ in keys]
    for a in range(n):
        for b in range(a + 1, n):
            if not ((adjacency[a] >> b) & 1):
                continue
            root_vertices = [v for v in range(n) if v != a and v != b]
            key, inverse = canon_label(root_order, induced(adjacency, root_vertices))
            root = root_id[key]
            base_a = [
                inverse[p]
                for p, vertex in enumerate(root_vertices)
                if (adjacency[a] >> vertex) & 1
            ]
            base_b = [
                inverse[p]
                for p, vertex in enumerate(root_vertices)
                if (adjacency[b] >> vertex) & 1
            ]
            same = 0
            for auto in automorphisms[root]:
                profile_a = tuple(sorted(auto[v] for v in base_a))
                profile_b = tuple(sorted(auto[v] for v in base_b))
                same += colour(key, profile_a) == colour(key, profile_b)
            result[root] += Fraction(same, len(automorphisms[root]))
    return tuple(result)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--random-trials", type=int, default=200)
    parser.add_argument("--exhaustive-through", type=int, default=0)
    args = parser.parse_args()
    witness_results = []
    for n, graph6, permutation, expected in WITNESSES:
        graph = decode_g6(graph6)
        relabelled = relabel_new_to_old(graph, permutation)
        before = raw_same_ordered(graph)
        after = raw_same_ordered(relabelled)
        edge_ordered = sum(row.bit_count() for row in graph)
        if (before, after, edge_ordered) != expected:
            raise AssertionError((n, before, after, edge_ordered, expected))
        aut_before = aut_averaged_signature(graph)
        aut_after = aut_averaged_signature(relabelled)
        if aut_before != aut_after:
            raise AssertionError(f"Aut average failed on frozen n={n} witness")
        witness_results.append(
            {
                "n": n,
                "graph6": graph6,
                "raw_before": f"{before}/{edge_ordered}",
                "raw_after": f"{after}/{edge_ordered}",
                "aut_averaged_equal": True,
            }
        )

    rng = random.Random(230011)
    random_cases = 0
    for n, graph6, _, _ in WITNESSES:
        graph = decode_g6(graph6)
        baseline = aut_averaged_signature(graph)
        for _ in range(args.random_trials):
            permutation = list(range(n))
            rng.shuffle(permutation)
            if aut_averaged_signature(relabel_new_to_old(graph, permutation)) != baseline:
                raise AssertionError((n, permutation))
            random_cases += 1
    exhaustive_cases = []
    if args.exhaustive_through:
        for n in range(4, args.exhaustive_through + 1):
            lines = geng_lines(n)
            graph6 = lines[(2 * len(lines)) // 3]
            graph = decode_g6(graph6)
            baseline = aut_averaged_signature(graph)
            count = 0
            for permutation in itertools.permutations(range(n)):
                if aut_averaged_signature(
                    relabel_new_to_old(graph, list(permutation))
                ) != baseline:
                    raise AssertionError((n, graph6, permutation))
                count += 1
            exhaustive_cases.append(
                {"n": n, "graph6": graph6, "relabelings": count}
            )
    print(
        json.dumps(
            {
                "verdict": "PASS",
                "raw_canonical_rule_invariant": False,
                "aut_averaged_rule_invariant_on_all_tests": True,
                "frozen_witnesses": witness_results,
                "additional_random_relabelings": random_cases,
                "exhaustive_fixture_relabelings": exhaustive_cases,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
