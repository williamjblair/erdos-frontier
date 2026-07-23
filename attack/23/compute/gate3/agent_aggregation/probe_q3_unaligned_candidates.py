#!/usr/bin/env python3
"""Exact check of the three q3 unaligned candidate types.

For a saturated size-three span-four block beginning at corridor coordinate
``l``, the only local same-side pairs not controlled by BFS-level separation
are expected to be

``A=(p[l+1],cR)``, ``B=(p[l+2],cM)``, ``C=(p[l+3],cL)``.

This probe checks every pure-mass q3 constructor through the requested
range.  Any two candidates being legal forces all four optional attachments
to be absent.  In that chordless case the complement of the canonical left
region at ``l`` has cut size two, separates the rooted terminals, and
separates all three candidates.  RFC therefore permits at most one candidate
type in any demand family.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import asdict
import json

from compute23.gate3.agent_d2s.two_defect_geometry_verify import (
    _distances,
    build,
    geometries,
)


MASS = {
    "q1s2": 1,
    "q1s0": 1,
    "q2s3": 2,
    "q2s2": 2,
    "q3s4": 3,
}


def run(max_s: int = 7) -> dict[str, object]:
    counts: Counter[str] = Counter()
    first: dict[str, object] = {}
    for geometry in geometries(range(3, max_s + 1)):
        if geometry.shape != "mass_q3":
            continue
        counts["constructors"] += 1
        built = build(geometry)
        distances = _distances(built)
        q3_index = next(
            index
            for index, block in enumerate(geometry.blocks)
            if block.kind == "q3s4"
        )
        q3 = geometry.blocks[q3_index]

        cursor = geometry.d + 1
        block_vertices: list[tuple[int, ...]] = []
        for block in geometry.blocks:
            vertices = tuple(range(cursor, cursor + MASS[block.kind]))
            block_vertices.append(vertices)
            cursor += MASS[block.kind]
        assert cursor == built.n
        c_left, c_middle, c_right = block_vertices[q3_index]
        candidates = (
            (q3.start + 1, c_right),
            (q3.start + 2, c_middle),
            (q3.start + 3, c_left),
        )
        legal = tuple(
            distances[u][v] >= 4
            and distances[0][u] % 2 == distances[0][v] % 2
            for u, v in candidates
        )
        legal_count = sum(legal)
        counts[f"legal_candidate_count_{legal_count}"] += 1
        if legal_count >= 2:
            counts["two_or_more_legal"] += 1
            if q3.option != 0:
                counts["two_legal_with_optional_attachment"] += 1
                first.setdefault(
                    "two_legal_with_optional_attachment",
                    {"geometry": asdict(geometry), "legal": legal},
                )

            left_region = set(range(q3.start + 1))
            for block, vertices in zip(
                geometry.blocks, block_vertices, strict=True
            ):
                if block.start <= q3.start:
                    left_region.update(vertices)
            cut = set(range(built.n)) - left_region
            cut_size = sum(
                (u in cut) != (v in cut) for u, v in built.edges
            )
            separates_terminals = (0 in cut) != (geometry.d in cut)
            separated_candidates = tuple(
                (u in cut) != (v in cut) for u, v in candidates
            )
            if not (
                q3.option == 0
                and cut_size == 2
                and separates_terminals
                and all(separated_candidates)
            ):
                counts["residual_cut_failures"] += 1
                first.setdefault(
                    "residual_cut_failure",
                    {
                        "geometry": asdict(geometry),
                        "edges": built.edges,
                        "cut": tuple(sorted(cut)),
                        "cut_size": cut_size,
                        "legal": legal,
                        "separated_candidates": separated_candidates,
                    },
                )
            else:
                # Each legal pair of candidate types contributes demand load
                # two, while the rooted terminal contributes one, against a
                # literal supply cut of size two.
                pair_count = legal_count * (legal_count - 1) // 2
                counts["candidate_pairs_killed_by_rfc_cut"] += pair_count

    return {
        "max_s": max_s,
        "counts": dict(counts),
        "first": first,
        "verdict": (
            "PASS"
            if not counts["two_legal_with_optional_attachment"]
            and not counts["residual_cut_failures"]
            else "FAIL"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-s", type=int, default=7)
    args = parser.parse_args()
    print(json.dumps(run(args.max_s), sort_keys=True))


if __name__ == "__main__":
    main()
