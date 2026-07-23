#!/usr/bin/env python3
"""Self-contained order-11 deletion lift for the Erdos #23 band.

This diagnostic deliberately avoids the unavailable ``horn_cert_state_it16``
cache.  It reconstructs two deterministic combinatorial objects with nauty:

* D_11, the vertex-deletion marginal T_11 -> T_10;
* the k=8 rooted profile decomposition of every edge in every T_10 type.

The ``solve-k8`` command maximizes the normalized bipartization excess using
only order-11 consistency and explicit k=8 profile-colouring cuts.  Every cut
emitted by the script is sound independently of whether the separation
heuristic finds the true best colouring.  Consequently an objective <= 0
would be a valid floating-point closure candidate, while a positive objective
is only an obstruction for this particular accumulated cut pool.

All graph counts in the caches are integers.  Floating values occur only in
the diagnostic LP.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import os
import pickle
import random
import subprocess
import tempfile
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, eye, hstack, vstack


GENG = "/opt/homebrew/bin/geng"
LABELG = "/opt/homebrew/bin/labelg"
N10 = 12_172
N11 = 105_071


def decode_g6(line: str) -> list[int]:
    """Decode graph6 for n <= 62 into adjacency bitmasks."""
    raw = [ord(c) - 63 for c in line.strip()]
    if not raw or raw[0] >= 63:
        raise ValueError("only the one-byte graph6 order is supported")
    n = raw[0]
    bits = [(x >> k) & 1 for x in raw[1:] for k in range(5, -1, -1)]
    adj = [0] * n
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                adj[i] |= 1 << j
                adj[j] |= 1 << i
            p += 1
    return adj


def encode_g6(adj: list[int]) -> str:
    """Encode adjacency bitmasks as graph6 for n <= 62."""
    n = len(adj)
    if not 0 <= n <= 62:
        raise ValueError(n)
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append((adj[i] >> j) & 1)
    while len(bits) % 6:
        bits.append(0)
    chars = [chr(n + 63)]
    for p in range(0, len(bits), 6):
        x = 0
        for b in bits[p : p + 6]:
            x = (x << 1) | b
        chars.append(chr(x + 63))
    return "".join(chars)


def induced(adj: list[int], vertices: list[int]) -> list[int]:
    out = [0] * len(vertices)
    for a, u in enumerate(vertices):
        for b in range(a + 1, len(vertices)):
            if (adj[u] >> vertices[b]) & 1:
                out[a] |= 1 << b
                out[b] |= 1 << a
    return out


def _permutation_colors(n: int, adjacency: list[int]) -> list[int]:
    """The pinned upstream U8 canonical-labelling refinement."""
    colour = [adjacency[v].bit_count() for v in range(n)]
    for _ in range(5):
        refined = [
            (
                colour[v],
                tuple(sorted(colour[u] for u in range(n) if (adjacency[v] >> u) & 1)),
            )
            for v in range(n)
        ]
        names = {value: i for i, value in enumerate(sorted(set(refined)))}
        colour = [names[value] for value in refined]
    matrix = [[1 if (adjacency[i] >> j) & 1 else 0 for j in range(n)] for i in range(n)]

    def multiply(left, right):
        return [
            [sum(left[i][k] * right[k][j] for k in range(n)) for j in range(n)]
            for i in range(n)
        ]

    square = multiply(matrix, matrix)
    cube = multiply(square, matrix)
    fourth = multiply(cube, matrix)
    signature = [
        (
            colour[v],
            sum(square[v]),
            sum(cube[v]),
            sum(fourth[v]),
            square[v][v],
            cube[v][v],
            fourth[v][v],
        )
        for v in range(n)
    ]
    names = {value: i for i, value in enumerate(sorted(set(signature)))}
    return [names[value] for value in signature]


def canon_label(n: int, adjacency: list[int]) -> tuple[tuple[int, ...], dict[int, int]]:
    """Pinned upstream canonical key plus old-vertex -> canonical-position map."""
    colour = _permutation_colors(n, adjacency)
    ordered = sorted(range(n), key=lambda vertex: colour[vertex])
    groups = []
    start = 0
    while start < n:
        end = start
        while end < n and colour[ordered[end]] == colour[ordered[start]]:
            end += 1
        groups.append(ordered[start:end])
        start = end
    best = None
    best_permutation = None
    for choices in itertools.product(*(itertools.permutations(group) for group in groups)):
        permutation = [vertex for block in choices for vertex in block]
        key = tuple(
            1 if (adjacency[permutation[a]] >> permutation[b]) & 1 else 0
            for a in range(n)
            for b in range(a + 1, n)
        )
        if best is None or key < best:
            best = key
            best_permutation = permutation
    assert best is not None and best_permutation is not None
    inverse = {old: position for position, old in enumerate(best_permutation)}
    return best, inverse


def geng_lines(n: int) -> list[str]:
    answer = subprocess.run(
        [GENG, "-q", "-t", str(n)], check=True, capture_output=True, text=True
    )
    return answer.stdout.splitlines()


def canonicalize(lines: list[str], partition: str | None = None) -> list[str]:
    """Canonicalize a batch with labelg, preserving input order."""
    command = [LABELG, "-q", "-g"]
    if partition is not None:
        command.append("-f" + partition)
    answer = subprocess.run(
        command,
        input="".join(line + "\n" for line in lines),
        check=True,
        capture_output=True,
        text=True,
    )
    output = answer.stdout.splitlines()
    if len(output) != len(lines):
        raise RuntimeError((len(lines), len(output), answer.stderr[-1000:]))
    return output


def cache_digest(row: np.ndarray, col: np.ndarray, count: np.ndarray) -> str:
    """Platform-stable digest of sorted integer triples."""
    order = np.lexsort((row, col))
    h = hashlib.sha256()
    for i in order:
        h.update(int(row[i]).to_bytes(4, "little"))
        h.update(int(col[i]).to_bytes(4, "little"))
        h.update(int(count[i]).to_bytes(1, "little"))
    return h.hexdigest()


def load_d11(path: Path) -> tuple[csr_matrix, np.ndarray]:
    data = np.load(path)
    n10, n11 = int(data["n10"]), int(data["n11"])
    if (n10, n11) != (N10, N11):
        raise AssertionError((n10, n11))
    count = np.rint(11 * data["val"]).astype(np.int8)
    if not np.array_equal(count.astype(float) / 11, data["val"]):
        raise AssertionError("D11 values are not exact deletion counts / 11")
    matrix = csr_matrix(
        (count.astype(float) / 11, (data["row"], data["col"])),
        shape=(n10, n11),
    )
    return matrix, count


def build_d11(path: Path) -> dict[str, object]:
    """Build the exact T11 -> T10 uniform vertex-deletion marginal."""
    lines10 = geng_lines(10)
    lines11 = geng_lines(11)
    if (len(lines10), len(lines11)) != (N10, N11):
        raise AssertionError((len(lines10), len(lines11)))
    canonical10 = canonicalize(lines10)
    row_of = {key: i for i, key in enumerate(canonical10)}
    if len(row_of) != N10:
        raise AssertionError("T10 canonical labels are not injective")

    deletion_lines: list[str] = []
    for line in lines11:
        adj = decode_g6(line)
        for vertex in range(11):
            deletion_lines.append(encode_g6(induced(adj, [v for v in range(11) if v != vertex])))
    canonical_deletions = canonicalize(deletion_lines)
    if len(canonical_deletions) != 11 * N11:
        raise AssertionError(len(canonical_deletions))

    rows: list[int] = []
    columns: list[int] = []
    counts: list[int] = []
    for column in range(N11):
        block = canonical_deletions[11 * column : 11 * (column + 1)]
        indices = np.asarray([row_of[key] for key in block], dtype=np.int32)
        unique, multiplicity = np.unique(indices, return_counts=True)
        rows.extend(int(x) for x in unique)
        columns.extend([column] * len(unique))
        counts.extend(int(x) for x in multiplicity)
    if len(rows) != 979_924:
        raise AssertionError(len(rows))
    count = np.asarray(counts, dtype=np.int8)
    np.savez_compressed(
        path,
        row=np.asarray(rows, dtype=np.int32),
        col=np.asarray(columns, dtype=np.int32),
        val=count.astype(float) / 11,
        n10=N10,
        n11=N11,
    )
    return audit_d11(path)


def audit_d11(path: Path) -> dict[str, object]:
    data = np.load(path)
    D, count = load_d11(path)
    column_counts = np.asarray(
        csr_matrix((count, (data["row"], data["col"])), shape=D.shape).sum(axis=0)
    ).ravel()
    report = {
        "shape": list(D.shape),
        "nnz": int(D.nnz),
        "integer_count_min": int(count.min()),
        "integer_count_max": int(count.max()),
        "column_count_min": int(column_counts.min()),
        "column_count_max": int(column_counts.max()),
        "integer_triple_sha256": cache_digest(data["row"], data["col"], count),
    }
    if report["column_count_min"] != 11 or report["column_count_max"] != 11:
        raise AssertionError(report)
    return report


def build_k8(cache: Path) -> dict[str, object]:
    """UNSAFE historical raw-canonical builder; retained only for falsification.

    Its rows fail relabel invariance.  User-facing commands do not call it.
    """
    lines10 = geng_lines(10)
    if len(lines10) != N10:
        raise AssertionError(len(lines10))
    graphs10 = [decode_g6(line) for line in lines10]
    entry_j: list[int] = []
    root_keys: list[tuple[int, ...]] = []
    profiles_a: list[tuple[int, ...]] = []
    profiles_b: list[tuple[int, ...]] = []
    memo: dict[tuple[int, ...], tuple[tuple[int, ...], dict[int, int]]] = {}
    for j, adj in enumerate(graphs10):
        for a in range(10):
            for b in range(a + 1, 10):
                if not ((adj[a] >> b) & 1):
                    continue
                root_vertices = [v for v in range(10) if v != a and v != b]
                root = induced(adj, root_vertices)
                memo_key = tuple(root)
                labelled = memo.get(memo_key)
                if labelled is None:
                    labelled = canon_label(8, root)
                    memo[memo_key] = labelled
                key, inverse = labelled
                root_keys.append(key)
                profiles_a.append(
                    tuple(
                        sorted(
                            inverse[position]
                            for position, vertex in enumerate(root_vertices)
                            if (adj[a] >> vertex) & 1
                        )
                    )
                )
                profiles_b.append(
                    tuple(
                        sorted(
                            inverse[position]
                            for position, vertex in enumerate(root_vertices)
                            if (adj[b] >> vertex) & 1
                        )
                    )
                )
                entry_j.append(j)
    if len(entry_j) != 160_238:
        raise AssertionError(len(entry_j))

    distinct_roots = sorted(set(root_keys))
    if len(distinct_roots) != 410:
        raise AssertionError(len(distinct_roots))
    root_id = {key: i for i, key in enumerate(distinct_roots)}
    rid = np.fromiter((root_id[key] for key in root_keys), np.int16)

    profile_maps: list[dict[tuple[int, ...], int]] = [dict() for _ in distinct_roots]
    pa = np.empty(len(entry_j), dtype=np.int16)
    pb = np.empty(len(entry_j), dtype=np.int16)
    for e, (r, ka, kb) in enumerate(zip(rid, profiles_a, profiles_b)):
        profile_map = profile_maps[int(r)]
        if ka not in profile_map:
            profile_map[ka] = len(profile_map)
        if kb not in profile_map:
            profile_map[kb] = len(profile_map)
        pa[e] = profile_map[ka]
        pb[e] = profile_map[kb]
    profile_count = np.asarray([len(m) for m in profile_maps], dtype=np.int16)
    if int(profile_count.max()) > np.iinfo(np.int16).max:
        raise AssertionError(int(profile_count.max()))

    np.savez_compressed(
        cache,
        entry_j=np.asarray(entry_j, dtype=np.int32),
        rid=rid,
        pa=pa,
        pb=pb,
        profile_count=profile_count,
        lines10=np.asarray(lines10),
    )
    return audit_k8(cache)


def build_k7_upstream(cache: Path) -> dict[str, object]:
    """Reconstruct pinned ``precompute_type`` k=7 E and S data on T9.

    Unlike U8's canonical-root rule, k7 averages over every ordered embedding
    of a fixed labelled type.  We enumerate root subsets and then its full
    automorphism group, which is exactly the same count with far less work
    than scanning all (9)_7 ordered tuples independently.
    """
    lines9 = geng_lines(9)
    if len(lines9) != 1_897:
        raise AssertionError(len(lines9))
    graphs9 = [decode_g6(line) for line in lines9]
    roots7 = [canon_label(7, decode_g6(line))[0] for line in geng_lines(7)]
    distinct_roots = sorted(set(roots7))
    if len(distinct_roots) != 107:
        raise AssertionError(len(distinct_roots))
    root_id = {key: i for i, key in enumerate(distinct_roots)}

    def adjacency_from_key(key: tuple[int, ...]) -> list[int]:
        adjacency = [0] * 7
        p = 0
        for a in range(7):
            for b in range(a + 1, 7):
                if key[p]:
                    adjacency[a] |= 1 << b
                    adjacency[b] |= 1 << a
                p += 1
        return adjacency

    automorphisms: list[list[tuple[int, ...]]] = []
    profile_maps: list[dict[int, int]] = []
    for key in distinct_roots:
        adjacency = adjacency_from_key(key)
        autos = []
        for permutation in itertools.permutations(range(7)):
            if all(
                ((adjacency[a] >> b) & 1)
                == ((adjacency[permutation[a]] >> permutation[b]) & 1)
                for a in range(7)
                for b in range(a + 1, 7)
            ):
                autos.append(permutation)
        automorphisms.append(autos)
        independent = []
        for mask in range(1 << 7):
            vertices = [v for v in range(7) if (mask >> v) & 1]
            if all(not ((adjacency[a] >> b) & 1) for a in vertices for b in vertices if a < b):
                independent.append(mask)
        profile_maps.append({mask: i for i, mask in enumerate(independent)})

    edge_counts: dict[tuple[int, int, int, int], int] = {}
    root_counts: dict[tuple[int, int], int] = {}
    memo: dict[tuple[int, ...], tuple[tuple[int, ...], dict[int, int]]] = {}
    for j, adj in enumerate(graphs9):
        for root_vertices_tuple in itertools.combinations(range(9), 7):
            root_vertices = list(root_vertices_tuple)
            outside = [v for v in range(9) if v not in root_vertices_tuple]
            a, b = outside
            root = induced(adj, root_vertices)
            memo_key = tuple(root)
            labelled = memo.get(memo_key)
            if labelled is None:
                labelled = canon_label(7, root)
                memo[memo_key] = labelled
            key, inverse = labelled
            root = root_id[key]
            autos = automorphisms[root]
            root_counts[(j, root)] = root_counts.get((j, root), 0) + len(autos)
            if not ((adj[a] >> b) & 1):
                continue
            base_a = [
                inverse[position]
                for position, vertex in enumerate(root_vertices)
                if (adj[a] >> vertex) & 1
            ]
            base_b = [
                inverse[position]
                for position, vertex in enumerate(root_vertices)
                if (adj[b] >> vertex) & 1
            ]
            mapping = profile_maps[root]
            for auto in autos:
                mask_a = sum(1 << auto[v] for v in base_a)
                mask_b = sum(1 << auto[v] for v in base_b)
                profile_a, profile_b = mapping[mask_a], mapping[mask_b]
                if profile_a > profile_b:
                    profile_a, profile_b = profile_b, profile_a
                item = (j, root, profile_a, profile_b)
                edge_counts[item] = edge_counts.get(item, 0) + 1

    edge_items = sorted(edge_counts)
    root_items = sorted(root_counts)
    profile_count = np.asarray([len(mapping) for mapping in profile_maps], dtype=np.int16)
    np.savez_compressed(
        cache,
        entry_j=np.asarray([item[0] for item in edge_items], dtype=np.int32),
        rid=np.asarray([item[1] for item in edge_items], dtype=np.int16),
        pa=np.asarray([item[2] for item in edge_items], dtype=np.int16),
        pb=np.asarray([item[3] for item in edge_items], dtype=np.int16),
        entry_count=np.asarray([edge_counts[item] for item in edge_items], dtype=np.int32),
        s_j=np.asarray([item[0] for item in root_items], dtype=np.int32),
        s_rid=np.asarray([item[1] for item in root_items], dtype=np.int16),
        s_count=np.asarray([root_counts[item] for item in root_items], dtype=np.int32),
        normalization=np.int64(math.prod(9 - i for i in range(7))),
        profile_count=profile_count,
        lines9=np.asarray(lines9),
    )
    return audit_k7_upstream(cache)


def build_k7(cache: Path) -> dict[str, object]:
    """UNSAFE historical grouped raw-coordinate k=7 builder.

    Although its all-one identity holds, arbitrary raw colours fail relabel
    invariance.  It is retained only to reproduce the dead route.
    """
    lines9 = geng_lines(9)
    if len(lines9) != 1_897:
        raise AssertionError(len(lines9))
    graphs9 = [decode_g6(line) for line in lines9]
    entry_j: list[int] = []
    root_keys: list[tuple[int, ...]] = []
    profiles_a: list[tuple[int, ...]] = []
    profiles_b: list[tuple[int, ...]] = []
    memo: dict[tuple[int, ...], tuple[tuple[int, ...], dict[int, int]]] = {}
    for j, adjacency in enumerate(graphs9):
        for a in range(9):
            for b in range(a + 1, 9):
                if not ((adjacency[a] >> b) & 1):
                    continue
                root_vertices = [v for v in range(9) if v != a and v != b]
                root = induced(adjacency, root_vertices)
                memo_key = tuple(root)
                labelled = memo.get(memo_key)
                if labelled is None:
                    labelled = canon_label(7, root)
                    memo[memo_key] = labelled
                key, inverse = labelled
                root_keys.append(key)
                profiles_a.append(
                    tuple(
                        sorted(
                            inverse[position]
                            for position, vertex in enumerate(root_vertices)
                            if (adjacency[a] >> vertex) & 1
                        )
                    )
                )
                profiles_b.append(
                    tuple(
                        sorted(
                            inverse[position]
                            for position, vertex in enumerate(root_vertices)
                            if (adjacency[b] >> vertex) & 1
                        )
                    )
                )
                entry_j.append(j)
    if len(entry_j) != 20_432:
        raise AssertionError(len(entry_j))
    distinct_roots = sorted(set(root_keys))
    if len(distinct_roots) != 107:
        raise AssertionError(len(distinct_roots))
    root_id = {key: i for i, key in enumerate(distinct_roots)}
    rid = np.fromiter((root_id[key] for key in root_keys), np.int16)
    profile_maps: list[dict[tuple[int, ...], int]] = [dict() for _ in distinct_roots]
    pa = np.empty(len(entry_j), dtype=np.int16)
    pb = np.empty(len(entry_j), dtype=np.int16)
    for e, (root, a, b) in enumerate(zip(rid, profiles_a, profiles_b)):
        mapping = profile_maps[int(root)]
        if a not in mapping:
            mapping[a] = len(mapping)
        if b not in mapping:
            mapping[b] = len(mapping)
        pa[e] = mapping[a]
        pb[e] = mapping[b]
    profile_count = np.asarray([len(mapping) for mapping in profile_maps], dtype=np.int16)
    np.savez_compressed(
        cache,
        entry_j=np.asarray(entry_j, dtype=np.int32),
        rid=rid,
        pa=pa,
        pb=pb,
        profile_count=profile_count,
        lines9=np.asarray(lines9),
    )
    return audit_k7(cache)


def audit_k8(cache: Path) -> dict[str, object]:
    data = np.load(cache)
    j = data["entry_j"]
    rid, pa, pb = data["rid"], data["pa"], data["pb"]
    profile_count = data["profile_count"]
    if not (len(j) == len(rid) == len(pa) == len(pb) == 160_238):
        raise AssertionError("entry lengths")
    edge_count = np.bincount(j, minlength=N10)
    lines10 = data["lines10"].tolist()
    independent_edges = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) // 2 for line in lines10]
    )
    if not np.array_equal(edge_count, independent_edges):
        raise AssertionError("all-one profile colouring does not reproduce edge density")
    if not all(
        0 <= pa[e] < profile_count[rid[e]] and 0 <= pb[e] < profile_count[rid[e]]
        for e in range(len(j))
    ):
        raise AssertionError("profile id out of range")
    h = hashlib.sha256()
    for arrays in (j, rid, pa, pb, profile_count):
        h.update(np.asarray(arrays).astype("<i4", copy=False).tobytes())
    return {
        "entries": int(len(j)),
        "root_types": int(len(profile_count)),
        "profile_count_min": int(profile_count.min()),
        "profile_count_max": int(profile_count.max()),
        "edge_count_min": int(edge_count.min()),
        "edge_count_max": int(edge_count.max()),
        "integer_arrays_sha256": h.hexdigest(),
    }


def audit_k7_upstream(cache: Path) -> dict[str, object]:
    data = np.load(cache)
    j, rid, pa, pb = data["entry_j"], data["rid"], data["pa"], data["pb"]
    entry_count = data["entry_count"]
    s_j, s_rid, s_count = data["s_j"], data["s_rid"], data["s_count"]
    normalization = int(data["normalization"])
    profile_count = data["profile_count"]
    if not (len(j) == len(rid) == len(pa) == len(pb) == len(entry_count)):
        raise AssertionError("entry lengths")
    if normalization != math.prod(9 - i for i in range(7)):
        raise AssertionError(normalization)
    if np.any(entry_count <= 0) or np.any(s_count <= 0):
        raise AssertionError("nonpositive multiplicity")
    e_total = csr_matrix((entry_count, (rid, j)), shape=(107, 1_897))
    s_total = csr_matrix((s_count, (s_rid, s_j)), shape=(107, 1_897))
    if (e_total > s_total).nnz:
        raise AssertionError("edge-root count exceeds root count")
    h = hashlib.sha256()
    for array in (
        j,
        rid,
        pa,
        pb,
        entry_count,
        s_j,
        s_rid,
        s_count,
        profile_count,
    ):
        h.update(np.asarray(array).astype("<i4", copy=False).tobytes())
    return {
        "aggregated_edge_entries": int(len(j)),
        "ordered_edge_embedding_count": int(entry_count.sum()),
        "root_count_entries": int(len(s_j)),
        "ordered_root_embedding_count": int(s_count.sum()),
        "normalization": normalization,
        "root_types": int(len(profile_count)),
        "profile_count_min": int(profile_count.min()),
        "profile_count_max": int(profile_count.max()),
        "integer_arrays_sha256": h.hexdigest(),
    }


def audit_k7(cache: Path) -> dict[str, object]:
    data = np.load(cache)
    j, rid, pa, pb = data["entry_j"], data["rid"], data["pa"], data["pb"]
    profile_count = data["profile_count"]
    if not (len(j) == len(rid) == len(pa) == len(pb) == 20_432):
        raise AssertionError("entry lengths")
    edge_count = np.bincount(j, minlength=1_897)
    independent_edges = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) // 2 for line in data["lines9"].tolist()]
    )
    if not np.array_equal(edge_count, independent_edges):
        raise AssertionError("all-one k7 rule does not equal e(H)/36 statewise")
    if not all(
        0 <= pa[e] < profile_count[rid[e]] and 0 <= pb[e] < profile_count[rid[e]]
        for e in range(len(j))
    ):
        raise AssertionError("profile id out of range")
    h = hashlib.sha256()
    for array in (j, rid, pa, pb, profile_count):
        h.update(np.asarray(array).astype("<i4", copy=False).tobytes())
    return {
        "entries": int(len(j)),
        "root_types": int(len(profile_count)),
        "profile_count_min": int(profile_count.min()),
        "profile_count_max": int(profile_count.max()),
        "edge_count_min": int(edge_count.min()),
        "edge_count_max": int(edge_count.max()),
        "all_one_identity": "sum_R L_R,all-one(H) = e(H)/36 for all 1897 T9 states",
        "integer_arrays_sha256": h.hexdigest(),
    }


def _root_catalog(root_order: int):
    """Canonical root keys, automorphisms, and independent-profile maps."""
    keys = sorted({canon_label(root_order, decode_g6(line))[0] for line in geng_lines(root_order)})

    def adjacency_from_key(key: tuple[int, ...]) -> list[int]:
        adjacency = [0] * root_order
        p = 0
        for a in range(root_order):
            for b in range(a + 1, root_order):
                if key[p]:
                    adjacency[a] |= 1 << b
                    adjacency[b] |= 1 << a
                p += 1
        return adjacency

    automorphisms = []
    profile_maps = []
    for key in keys:
        adjacency = adjacency_from_key(key)
        autos = []
        for permutation in itertools.permutations(range(root_order)):
            if all(
                ((adjacency[a] >> b) & 1)
                == ((adjacency[permutation[a]] >> permutation[b]) & 1)
                for a in range(root_order)
                for b in range(a + 1, root_order)
            ):
                autos.append(permutation)
        independent = []
        for mask in range(1 << root_order):
            vertices = [v for v in range(root_order) if (mask >> v) & 1]
            if all(
                not ((adjacency[a] >> b) & 1)
                for a in vertices
                for b in vertices
                if a < b
            ):
                independent.append(mask)
        automorphisms.append(autos)
        profile_maps.append({mask: i for i, mask in enumerate(independent)})
    return keys, automorphisms, profile_maps


def build_aut_averaged(cache: Path, state_order: int) -> dict[str, object]:
    """Build the relabel-invariant Aut(R)-averaged grouped profile envelope."""
    if state_order not in (9, 10):
        raise ValueError(state_order)
    root_order = state_order - 2
    expected_states = {9: 1_897, 10: N10}[state_order]
    expected_roots = {9: 107, 10: 410}[state_order]
    lines = geng_lines(state_order)
    if len(lines) != expected_states:
        raise AssertionError(len(lines))
    graphs = [decode_g6(line) for line in lines]
    root_keys, automorphisms, profile_maps = _root_catalog(root_order)
    if len(root_keys) != expected_roots:
        raise AssertionError(len(root_keys))
    root_id = {key: i for i, key in enumerate(root_keys)}
    memo: dict[tuple[int, ...], tuple[tuple[int, ...], dict[int, int]]] = {}
    accumulator: dict[tuple[int, int, int, int], int] = {}
    for j, adjacency in enumerate(graphs):
        for a in range(state_order):
            for b in range(a + 1, state_order):
                if not ((adjacency[a] >> b) & 1):
                    continue
                root_vertices = [v for v in range(state_order) if v != a and v != b]
                root_graph = induced(adjacency, root_vertices)
                memo_key = tuple(root_graph)
                labelled = memo.get(memo_key)
                if labelled is None:
                    labelled = canon_label(root_order, root_graph)
                    memo[memo_key] = labelled
                key, inverse = labelled
                root = root_id[key]
                base_a = [
                    inverse[position]
                    for position, vertex in enumerate(root_vertices)
                    if (adjacency[a] >> vertex) & 1
                ]
                base_b = [
                    inverse[position]
                    for position, vertex in enumerate(root_vertices)
                    if (adjacency[b] >> vertex) & 1
                ]
                mapping = profile_maps[root]
                for auto in automorphisms[root]:
                    mask_a = sum(1 << auto[v] for v in base_a)
                    mask_b = sum(1 << auto[v] for v in base_b)
                    pa, pb = mapping[mask_a], mapping[mask_b]
                    if pa > pb:
                        pa, pb = pb, pa
                    item = (j, root, pa, pb)
                    accumulator[item] = accumulator.get(item, 0) + 1
    items = sorted(accumulator)
    np.savez_compressed(
        cache,
        entry_j=np.asarray([item[0] for item in items], dtype=np.int32),
        rid=np.asarray([item[1] for item in items], dtype=np.int16),
        pa=np.asarray([item[2] for item in items], dtype=np.int16),
        pb=np.asarray([item[3] for item in items], dtype=np.int16),
        entry_count=np.asarray([accumulator[item] for item in items], dtype=np.int32),
        aut_size=np.asarray([len(autos) for autos in automorphisms], dtype=np.int32),
        profile_count=np.asarray([len(mapping) for mapping in profile_maps], dtype=np.int16),
        root_keys=np.asarray(root_keys, dtype=np.int8),
        state_order=np.int64(state_order),
        lines=np.asarray(lines),
    )
    return audit_aut_averaged(cache)


def audit_aut_averaged(cache: Path) -> dict[str, object]:
    data = np.load(cache)
    state_order = int(data["state_order"])
    root_order = state_order - 2
    expected_states = {9: 1_897, 10: N10}[state_order]
    expected_roots = {9: 107, 10: 410}[state_order]
    j, rid = data["entry_j"], data["rid"]
    pa, pb, count = data["pa"], data["pb"], data["entry_count"]
    aut_size, profile_count = data["aut_size"], data["profile_count"]
    if not (len(j) == len(rid) == len(pa) == len(pb) == len(count)):
        raise AssertionError("entry lengths")
    if len(aut_size) != expected_roots or len(profile_count) != expected_roots:
        raise AssertionError("root count")
    # Exact coefficientwise all-one identity: each edge contributes the full
    # automorphism-group size, then is divided by that same size.
    numerator_by_state = [Fraction() for _ in range(expected_states)]
    choose_two = math.comb(state_order, 2)
    for state, root, multiplicity in zip(j, rid, count):
        numerator_by_state[int(state)] += Fraction(
            int(multiplicity), choose_two * int(aut_size[int(root)])
        )
    independent_edges = [
        sum(x.bit_count() for x in decode_g6(line)) // 2 for line in data["lines"].tolist()
    ]
    if any(
        numerator_by_state[state] != Fraction(independent_edges[state], choose_two)
        for state in range(expected_states)
    ):
        raise AssertionError("all-one identity failed")
    h = hashlib.sha256()
    for array in (j, rid, pa, pb, count, aut_size, profile_count, data["root_keys"]):
        h.update(np.asarray(array).astype("<i4", copy=False).tobytes())
    return {
        "state_order": state_order,
        "root_order": root_order,
        "states": expected_states,
        "root_types": expected_roots,
        "aggregated_entries": int(len(j)),
        "automorphism_expanded_entries": int(count.sum()),
        "aut_size_min": int(aut_size.min()),
        "aut_size_max": int(aut_size.max()),
        "profile_count_min": int(profile_count.min()),
        "profile_count_max": int(profile_count.max()),
        "all_one_identity": f"sum_R L_R,all-one(H) = e(H)/C({state_order},2) for every state",
        "integer_arrays_sha256": h.hexdigest(),
    }


def build_orbit_invariant(cache: Path, state_order: int) -> dict[str, object]:
    """Build the sound profile-orbit envelope using coloured canonical extensions."""
    if state_order not in (9, 10):
        raise ValueError(state_order)
    root_order = state_order - 2
    expected_states = {9: 1_897, 10: N10}[state_order]
    expected_roots = {9: 107, 10: 410}[state_order]
    lines = geng_lines(state_order)
    if len(lines) != expected_states:
        raise AssertionError(len(lines))
    entry_j = []
    roots = []
    extension_a = []
    extension_b = []
    for j, line in enumerate(lines):
        adjacency = decode_g6(line)
        for a in range(state_order):
            for b in range(a + 1, state_order):
                if not ((adjacency[a] >> b) & 1):
                    continue
                root_vertices = [v for v in range(state_order) if v != a and v != b]
                roots.append(encode_g6(induced(adjacency, root_vertices)))
                extension_a.append(encode_g6(induced(adjacency, root_vertices + [a])))
                extension_b.append(encode_g6(induced(adjacency, root_vertices + [b])))
                entry_j.append(j)
    canonical_roots = canonicalize(roots)
    partition = "a" * root_order + "b"
    canonical_a = canonicalize(extension_a, partition)
    canonical_b = canonicalize(extension_b, partition)
    root_keys = sorted(set(canonical_roots))
    if len(root_keys) != expected_roots:
        raise AssertionError(len(root_keys))
    root_id = {key: i for i, key in enumerate(root_keys)}
    rid = np.fromiter((root_id[key] for key in canonical_roots), np.int16)
    profile_maps: list[dict[str, int]] = [dict() for _ in root_keys]
    pa = np.empty(len(entry_j), dtype=np.int16)
    pb = np.empty(len(entry_j), dtype=np.int16)
    for e, (root, a, b) in enumerate(zip(rid, canonical_a, canonical_b)):
        mapping = profile_maps[int(root)]
        if a not in mapping:
            mapping[a] = len(mapping)
        if b not in mapping:
            mapping[b] = len(mapping)
        pa[e] = mapping[a]
        pb[e] = mapping[b]
    np.savez_compressed(
        cache,
        entry_j=np.asarray(entry_j, dtype=np.int32),
        rid=rid,
        pa=pa,
        pb=pb,
        profile_count=np.asarray([len(mapping) for mapping in profile_maps], dtype=np.int16),
        state_order=np.int64(state_order),
        lines=np.asarray(lines),
    )
    return audit_orbit_invariant(cache)


def audit_orbit_invariant(cache: Path) -> dict[str, object]:
    data = np.load(cache)
    state_order = int(data["state_order"])
    expected_states = {9: 1_897, 10: N10}[state_order]
    expected_roots = {9: 107, 10: 410}[state_order]
    j, rid, pa, pb = data["entry_j"], data["rid"], data["pa"], data["pb"]
    profile_count = data["profile_count"]
    if not (len(j) == len(rid) == len(pa) == len(pb)):
        raise AssertionError("entry lengths")
    edge_count = np.bincount(j, minlength=expected_states)
    independent_edges = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) // 2 for line in data["lines"].tolist()]
    )
    if not np.array_equal(edge_count, independent_edges):
        raise AssertionError("all-one identity")
    h = hashlib.sha256()
    for array in (j, rid, pa, pb, profile_count):
        h.update(np.asarray(array).astype("<i4", copy=False).tobytes())
    return {
        "state_order": state_order,
        "root_order": state_order - 2,
        "states": expected_states,
        "root_types": expected_roots,
        "entries": int(len(j)),
        "profile_count_min": int(profile_count.min()),
        "profile_count_max": int(profile_count.max()),
        "all_one_identity": f"sum_R L_R,all-one(H) = e(H)/C({state_order},2) for every state",
        "integer_arrays_sha256": h.hexdigest(),
    }


def local_maxcut(
    n: int,
    left: np.ndarray,
    right: np.ndarray,
    weight: np.ndarray,
    seed: int,
    starts: int = 12,
) -> np.ndarray:
    """Deterministic multi-start one-flip local search for weighted MaxCut."""
    if n == 0:
        return np.zeros(0, dtype=np.int8)
    adjacency: list[list[tuple[int, float]]] = [[] for _ in range(n)]
    for a, b, w in zip(left, right, weight):
        a, b, w = int(a), int(b), float(w)
        if a == b or w <= 0:
            continue
        adjacency[a].append((b, w))
        adjacency[b].append((a, w))
    rng = random.Random(seed)
    candidates = [np.zeros(n, dtype=np.int8)]
    # Useful structured starts, then deterministic pseudorandom starts.
    candidates.append(np.arange(n, dtype=np.int8) & 1)
    for _ in range(max(0, starts - len(candidates))):
        candidates.append(np.asarray([rng.randrange(2) for _ in range(n)], dtype=np.int8))

    best = candidates[0]
    best_value = -1.0
    for color in candidates:
        color = color.copy()
        while True:
            best_gain = 1e-14
            best_vertex = -1
            for v in range(n):
                gain = 0.0
                cv = int(color[v])
                for w, value in adjacency[v]:
                    gain += value if cv == int(color[w]) else -value
                if gain > best_gain:
                    best_gain, best_vertex = gain, v
            if best_vertex < 0:
                break
            color[best_vertex] ^= 1
        value = sum(
            float(w)
            for a, b, w in zip(left, right, weight)
            if a != b and color[int(a)] != color[int(b)]
        )
        if value > best_value + 1e-14:
            best_value, best = value, color.copy()
    return best


def solve_k8(d11_cache: Path, k8_cache: Path, max_iterations: int) -> dict[str, object]:
    D, _ = load_d11(d11_cache)
    data = np.load(k8_cache)
    entry_j = data["entry_j"].astype(np.int32)
    rid = data["rid"].astype(np.int32)
    pa = data["pa"].astype(np.int32)
    pb = data["pb"].astype(np.int32)
    profile_count = data["profile_count"].astype(np.int32)
    lines10 = data["lines10"].tolist()
    edge_density = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) / 90 for line in lines10],
        dtype=float,
    )

    n10, n11, nr = N10, N11, len(profile_count)
    # Variables are [r(T11), q(T10), u(root types), eta].
    R0, Q0, U0, ETA = 0, n11, n11 + n10, n11 + n10 + nr
    nv = ETA + 1
    minus_identity = -eye(n10, format="csr")
    equality = hstack([D, minus_identity, csr_matrix((n10, nr + 1))], format="csr")
    sum_r = csr_matrix(
        (np.ones(n11), (np.zeros(n11, dtype=int), np.arange(n11))), shape=(1, nv)
    )
    A_eq = vstack([equality, sum_r], format="csr")
    b_eq = np.concatenate([np.zeros(n10), [1.0]])

    static_rows = []
    static_b = []
    row = np.zeros(nv)
    row[Q0 : Q0 + n10] = edge_density
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(0.3197)
    static_rows.append(csr_matrix((-row).reshape(1, -1)))
    static_b.append(-0.2486)
    row = np.zeros(nv)
    row[U0 : U0 + nr] = -1
    row[ETA] = 1
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(-2 / 25)

    cuts: list[csr_matrix] = []
    cut_meta: list[tuple[int, np.ndarray]] = []

    def add_cut(root: int, color: np.ndarray) -> None:
        mask = rid == root
        selected_entries = np.flatnonzero(mask)
        same = color[pa[mask]] == color[pb[mask]]
        coefficient = (
            np.bincount(entry_j[selected_entries[same]], minlength=n10).astype(float) / 45
        )
        row = np.zeros(nv)
        row[U0 + root] = 1
        row[Q0 : Q0 + n10] = -coefficient
        cuts.append(csr_matrix(row.reshape(1, -1)))
        cut_meta.append((root, color.copy()))

    # One valid cap for every root type is required to avoid unbounded u_R.
    for root in range(nr):
        add_cut(root, np.zeros(int(profile_count[root]), dtype=np.int8))

    objective = np.zeros(nv)
    objective[ETA] = -1
    bounds = [(0, None)] * ETA + [(None, None)]
    history = []
    final = None
    for iteration in range(max_iterations + 1):
        A_ub = vstack(static_rows + cuts, format="csr")
        b_ub = np.concatenate([np.asarray(static_b), np.zeros(len(cuts))])
        started = time.time()
        answer = linprog(
            objective,
            A_ub=A_ub,
            b_ub=b_ub,
            A_eq=A_eq,
            b_eq=b_eq,
            bounds=bounds,
            method="highs",
        )
        if not answer.success:
            raise RuntimeError(answer.message)
        final = answer
        q = np.asarray(answer.x[Q0 : Q0 + n10])
        u = np.asarray(answer.x[U0 : U0 + nr])
        eta = -float(answer.fun)
        added = 0
        worst_violation = 0.0
        for root in range(nr):
            mask = rid == root
            if not np.any(mask):
                continue
            # Aggregate repeated profile-pair occurrences under q.
            aa = np.minimum(pa[mask], pb[mask])
            bb = np.maximum(pa[mask], pb[mask])
            key = aa.astype(np.int64) * int(profile_count[root]) + bb
            unique, inverse = np.unique(key, return_inverse=True)
            weight = np.bincount(inverse, weights=q[entry_j[mask]]) / 45
            left = unique // int(profile_count[root])
            right = unique % int(profile_count[root])
            color = local_maxcut(
                int(profile_count[root]), left, right, weight, seed=1009 * iteration + root
            )
            same = color[pa[mask]] == color[pb[mask]]
            landing = float(q[entry_j[mask][same]].sum() / 45)
            violation = float(u[root] - landing)
            worst_violation = max(worst_violation, violation)
            if violation > 1e-9:
                add_cut(root, color)
                added += 1
        record = {
            "iteration": iteration,
            "eta": eta,
            "cuts": len(cuts),
            "added": added,
            "worst_violation": worst_violation,
            "solve_seconds": time.time() - started,
            "q_support_1e-10": int((q > 1e-10).sum()),
        }
        history.append(record)
        print(json.dumps(record, sort_keys=True), flush=True)
        if added == 0 or eta <= 0:
            break
    assert final is not None
    return {
        "verdict": "FLOAT_CLOSURE_CANDIDATE" if history[-1]["eta"] <= 0 else "NOT_CLOSED",
        "final_eta": history[-1]["eta"],
        "iterations": len(history),
        "cut_count": len(cuts),
        "history": history,
        "scope": "order11 deletion consistency plus explicit k8 profile-colouring cuts only",
    }


def solve_selective(
    d11_cache: Path, k8_cache: Path, max_iterations: int
) -> dict[str, object]:
    """Cutting-plane form of the order-11 lift, retaining only q variables.

    Infeasible q candidates are separated from ``cone(columns(D11))`` by the
    exact dual of an L1 projection LP.  This is equivalent to progressively
    adding order-11 consistency inequalities and is far smaller than carrying
    all 105,071 extension variables in the master LP.
    """
    D, _ = load_d11(d11_cache)
    data = np.load(k8_cache)
    entry_j = data["entry_j"].astype(np.int32)
    rid = data["rid"].astype(np.int32)
    pa = data["pa"].astype(np.int32)
    pb = data["pb"].astype(np.int32)
    profile_count = data["profile_count"].astype(np.int32)
    lines10 = data["lines10"].tolist()
    edge_density = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) / 90 for line in lines10]
    )

    nr = len(profile_count)
    Q0, U0, ETA = 0, N10, N10 + nr
    nv = ETA + 1
    static_rows: list[csr_matrix] = []
    static_b: list[float] = []
    row = np.zeros(nv)
    row[:N10] = edge_density
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(0.3197)
    static_rows.append(csr_matrix((-row).reshape(1, -1)))
    static_b.append(-0.2486)
    row = np.zeros(nv)
    row[U0 : U0 + nr] = -1
    row[ETA] = 1
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(-2 / 25)

    cuts: list[csr_matrix] = []
    cut_b: list[float] = []
    k8_cut_count = 0
    order11_cut_count = 0

    def add_k8_cut(root: int, color: np.ndarray) -> None:
        nonlocal k8_cut_count
        mask = rid == root
        entries = np.flatnonzero(mask)
        same = color[pa[mask]] == color[pb[mask]]
        coefficient = np.bincount(entry_j[entries[same]], minlength=N10) / 45
        row = np.zeros(nv)
        row[U0 + root] = 1
        row[:N10] = -coefficient
        cuts.append(csr_matrix(row.reshape(1, -1)))
        cut_b.append(0.0)
        k8_cut_count += 1

    for root in range(nr):
        add_k8_cut(root, np.zeros(int(profile_count[root]), dtype=np.int8))

    # min ||D r-q||_1, with dual D^T y<=0 and |y|<=1.
    l1_matrix = hstack([D, eye(N10, format="csr"), -eye(N10, format="csr")], format="csr")
    l1_objective = np.concatenate([np.zeros(N11), np.ones(2 * N10)])

    objective = np.zeros(nv)
    objective[ETA] = -1
    equality = csr_matrix(
        (np.ones(N10), (np.zeros(N10, dtype=int), np.arange(N10))), shape=(1, nv)
    )
    history = []
    for iteration in range(max_iterations + 1):
        A_ub = vstack(static_rows + cuts, format="csr")
        b_ub = np.concatenate([np.asarray(static_b), np.asarray(cut_b)])
        started = time.time()
        answer = linprog(
            objective,
            A_ub=A_ub,
            b_ub=b_ub,
            A_eq=equality,
            b_eq=[1.0],
            bounds=[(0, None)] * ETA + [(None, None)],
            method="highs",
        )
        if not answer.success:
            raise RuntimeError(answer.message)
        q = np.asarray(answer.x[:N10])
        u = np.asarray(answer.x[U0 : U0 + nr])
        eta = -float(answer.fun)

        k8_added = 0
        worst_k8 = 0.0
        for root in range(nr):
            mask = rid == root
            aa = np.minimum(pa[mask], pb[mask])
            bb = np.maximum(pa[mask], pb[mask])
            key = aa.astype(np.int64) * int(profile_count[root]) + bb
            unique, inverse = np.unique(key, return_inverse=True)
            weight = np.bincount(inverse, weights=q[entry_j[mask]]) / 45
            left = unique // int(profile_count[root])
            right = unique % int(profile_count[root])
            color = local_maxcut(
                int(profile_count[root]), left, right, weight, seed=1009 * iteration + root
            )
            same = color[pa[mask]] == color[pb[mask]]
            landing = float(q[entry_j[mask][same]].sum() / 45)
            violation = float(u[root] - landing)
            worst_k8 = max(worst_k8, violation)
            if violation > 1e-9:
                add_k8_cut(root, color)
                k8_added += 1

        projection = linprog(
            l1_objective,
            A_eq=l1_matrix,
            b_eq=q,
            bounds=(0, None),
            method="highs",
        )
        if not projection.success:
            raise RuntimeError(projection.message)
        distance = float(projection.fun)
        order11_added = 0
        if distance > 1e-9:
            y = np.asarray(projection.eqlin.marginals)
            upper = float(np.max(np.asarray(D.T @ y).ravel()))
            row = np.zeros(nv)
            row[:N10] = y
            cuts.append(csr_matrix(row.reshape(1, -1)))
            cut_b.append(upper)
            order11_cut_count += 1
            order11_added = 1
        record = {
            "iteration": iteration,
            "eta": eta,
            "k8_added": k8_added,
            "order11_added": order11_added,
            "k8_cut_count": k8_cut_count,
            "order11_cut_count": order11_cut_count,
            "order11_l1_distance": distance,
            "worst_k8_violation": worst_k8,
            "solve_and_separate_seconds": time.time() - started,
            "q_support_1e-10": int((q > 1e-10).sum()),
        }
        history.append(record)
        print(json.dumps(record, sort_keys=True), flush=True)
        if eta <= 0 or (k8_added == 0 and order11_added == 0):
            break
    return {
        "verdict": "FLOAT_CLOSURE_CANDIDATE" if history[-1]["eta"] <= 0 else "NOT_CLOSED",
        "final_eta": history[-1]["eta"],
        "iterations": len(history),
        "k8_cut_count": k8_cut_count,
        "order11_cut_count": order11_cut_count,
        "history": history,
        "scope": "selective order11 deletion cuts plus explicit k8 profile-colouring cuts",
    }


def solve_eliminated(
    d11_cache: Path, k8_cache: Path, max_iterations: int
) -> dict[str, object]:
    """Exact order-11 master with q=D11*r eliminated algebraically."""
    D, _ = load_d11(d11_cache)
    DT = D.T.tocsr()
    data = np.load(k8_cache)
    entry_j = data["entry_j"].astype(np.int32)
    rid = data["rid"].astype(np.int32)
    pa = data["pa"].astype(np.int32)
    pb = data["pb"].astype(np.int32)
    profile_count = data["profile_count"].astype(np.int32)
    lines10 = data["lines10"].tolist()
    edge_density = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) / 90 for line in lines10]
    )
    edge_on_r = np.asarray(DT @ edge_density).ravel()

    nr = len(profile_count)
    R0, U0, ETA = 0, N11, N11 + nr
    nv = ETA + 1
    static_rows: list[csr_matrix] = []
    static_b: list[float] = []
    row = np.zeros(nv)
    row[:N11] = edge_on_r
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(0.3197)
    static_rows.append(csr_matrix((-row).reshape(1, -1)))
    static_b.append(-0.2486)
    row = np.zeros(nv)
    row[U0 : U0 + nr] = -1
    row[ETA] = 1
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(-2 / 25)

    cuts: list[csr_matrix] = []

    def add_cut(root: int, color: np.ndarray) -> None:
        mask = rid == root
        entries = np.flatnonzero(mask)
        same = color[pa[mask]] == color[pb[mask]]
        coefficient_q = np.bincount(entry_j[entries[same]], minlength=N10) / 45
        coefficient_r = np.asarray(DT @ coefficient_q).ravel()
        nz = np.flatnonzero(coefficient_r)
        columns = np.concatenate([nz, [U0 + root]])
        values = np.concatenate([-coefficient_r[nz], [1.0]])
        cuts.append(
            csr_matrix((values, (np.zeros(len(columns), dtype=int), columns)), shape=(1, nv))
        )

    for root in range(nr):
        add_cut(root, np.zeros(int(profile_count[root]), dtype=np.int8))

    objective = np.zeros(nv)
    objective[ETA] = -1
    equality = csr_matrix(
        (np.ones(N11), (np.zeros(N11, dtype=int), np.arange(N11))), shape=(1, nv)
    )
    history = []
    final_r = None
    final_q = None
    for iteration in range(max_iterations + 1):
        A_ub = vstack(static_rows + cuts, format="csr")
        b_ub = np.concatenate([np.asarray(static_b), np.zeros(len(cuts))])
        started = time.time()
        answer = linprog(
            objective,
            A_ub=A_ub,
            b_ub=b_ub,
            A_eq=equality,
            b_eq=[1.0],
            bounds=[(0, None)] * ETA + [(None, None)],
            method="highs",
        )
        if not answer.success:
            raise RuntimeError(answer.message)
        r = np.asarray(answer.x[:N11])
        q = np.asarray(D @ r).ravel()
        u = np.asarray(answer.x[U0 : U0 + nr])
        eta = -float(answer.fun)
        final_r, final_q = r, q
        added = 0
        worst_violation = 0.0
        for root in range(nr):
            mask = rid == root
            aa = np.minimum(pa[mask], pb[mask])
            bb = np.maximum(pa[mask], pb[mask])
            key = aa.astype(np.int64) * int(profile_count[root]) + bb
            unique, inverse = np.unique(key, return_inverse=True)
            weight = np.bincount(inverse, weights=q[entry_j[mask]]) / 45
            left = unique // int(profile_count[root])
            right = unique % int(profile_count[root])
            color = local_maxcut(
                int(profile_count[root]), left, right, weight, seed=1009 * iteration + root
            )
            same = color[pa[mask]] == color[pb[mask]]
            landing = float(q[entry_j[mask][same]].sum() / 45)
            violation = float(u[root] - landing)
            worst_violation = max(worst_violation, violation)
            if violation > 1e-9:
                add_cut(root, color)
                added += 1
        independently_recomputed_eta = float(u.sum() - 2 / 25)
        record = {
            "iteration": iteration,
            "eta": eta,
            "eta_from_u_sum": independently_recomputed_eta,
            "eta_recompute_error": abs(eta - independently_recomputed_eta),
            "cuts": len(cuts),
            "added": added,
            "worst_k8_violation": worst_violation,
            "solve_and_separate_seconds": time.time() - started,
            "r_support_1e-10": int((r > 1e-10).sum()),
            "q_support_1e-10": int((q > 1e-10).sum()),
            "edge_density": float(edge_density @ q),
        }
        history.append(record)
        print(json.dumps(record, sort_keys=True), flush=True)
        if eta <= 0 or added == 0:
            break
    assert final_r is not None and final_q is not None
    return {
        "verdict": "FLOAT_CLOSURE_CANDIDATE" if history[-1]["eta"] <= 0 else "NOT_CLOSED",
        "final_eta": history[-1]["eta"],
        "iterations": len(history),
        "cut_count": len(cuts),
        "history": history,
        "final_r_support_1e-10": int((final_r > 1e-10).sum()),
        "final_q_support_1e-10": int((final_q > 1e-10).sum()),
        "scope": "full order11 deletion consistency plus explicit k8 profile-colouring cuts",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    build11 = sub.add_parser("build-d11")
    build11.add_argument("cache", type=Path)
    audit = sub.add_parser("audit-d11")
    audit.add_argument("cache", type=Path)
    build = sub.add_parser("build-k8")
    build.add_argument("cache", type=Path)
    build7 = sub.add_parser("build-k7")
    build7.add_argument("cache", type=Path)
    build7a = sub.add_parser("build-k7-aut")
    build7a.add_argument("cache", type=Path)
    build8a = sub.add_parser("build-k8-aut")
    build8a.add_argument("cache", type=Path)
    audita = sub.add_parser("audit-aut")
    audita.add_argument("cache", type=Path)
    build7o = sub.add_parser("build-k7-orbit")
    build7o.add_argument("cache", type=Path)
    build8o = sub.add_parser("build-k8-orbit")
    build8o.add_argument("cache", type=Path)
    audito = sub.add_parser("audit-orbit")
    audito.add_argument("cache", type=Path)
    audit8 = sub.add_parser("audit-k8")
    audit8.add_argument("cache", type=Path)
    solve = sub.add_parser("solve-k8")
    solve.add_argument("d11_cache", type=Path)
    solve.add_argument("k8_cache", type=Path)
    solve.add_argument("--max-iterations", type=int, default=20)
    selective = sub.add_parser("solve-selective")
    selective.add_argument("d11_cache", type=Path)
    selective.add_argument("k8_cache", type=Path)
    selective.add_argument("--max-iterations", type=int, default=20)
    eliminated = sub.add_parser("solve-eliminated")
    eliminated.add_argument("d11_cache", type=Path)
    eliminated.add_argument("k8_cache", type=Path)
    eliminated.add_argument("--max-iterations", type=int, default=20)
    args = parser.parse_args()
    if args.command == "build-d11":
        result = build_d11(args.cache)
    elif args.command == "audit-d11":
        result = audit_d11(args.cache)
    elif args.command == "build-k8":
        result = build_orbit_invariant(args.cache, 10)
    elif args.command == "build-k7":
        result = build_orbit_invariant(args.cache, 9)
    elif args.command == "build-k7-aut":
        result = build_aut_averaged(args.cache, 9)
    elif args.command == "build-k8-aut":
        result = build_aut_averaged(args.cache, 10)
    elif args.command == "audit-aut":
        result = audit_aut_averaged(args.cache)
    elif args.command == "build-k7-orbit":
        result = build_orbit_invariant(args.cache, 9)
    elif args.command == "build-k8-orbit":
        result = build_orbit_invariant(args.cache, 10)
    elif args.command == "audit-orbit":
        result = audit_orbit_invariant(args.cache)
    elif args.command == "audit-k8":
        result = audit_orbit_invariant(args.cache)
    elif args.command == "solve-k8":
        raise SystemExit("disabled: raw canonical profile rows fail relabel invariance; use order11_combined_master.py with orbit/Aut caches")
    elif args.command == "solve-selective":
        raise SystemExit("disabled: historical raw-profile diagnostic; use sound orbit/Aut caches")
    else:
        raise SystemExit("disabled: historical raw-profile diagnostic; use order11_combined_master.py")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
