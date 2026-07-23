"""Erdős #617, r = 5 instance: 5-colorings of E(K_26).

A counterexample to the conjecture is a coloring such that every 6-vertex
subset induces all 5 colors — equivalently alpha(G_c) <= 5 for every color
class G_c.  This module is the EXACT reference model and independent
verifier; everything else in the campaign must validate against it.
"""

from itertools import combinations

N = 26
R = 5
VERTS = list(range(N))
EDGES = list(combinations(VERTS, 2))          # 325 edges, lex order
EDGE_INDEX = {e: k for k, e in enumerate(EDGES)}


def edge_id(u, v):
    return EDGE_INDEX[(u, v) if u < v else (v, u)]


def color_classes(coloring):
    """coloring: list/tuple of length 325 with values in 0..4 ->
    adjacency bitmasks per color: masks[c][v] = bitmask of neighbours."""
    masks = [[0] * N for _ in range(R)]
    for k, c in enumerate(coloring):
        u, v = EDGES[k]
        masks[c][u] |= 1 << v
        masks[c][v] |= 1 << u
    return masks


def max_independent_at_least(adj, size):
    """True iff the graph (adjacency bitmask list) has an independent set
    of cardinality `size`.  Branch and bound on candidate bitmask."""
    full = (1 << N) - 1

    def rec(chosen, cand):
        if chosen == size:
            return True
        # not enough candidates left
        if chosen + bin(cand).count("1") < size:
            return False
        while cand:
            v = (cand & -cand).bit_length() - 1
            cand &= cand - 1
            if rec(chosen + 1, cand & ~adj[v]):
                return True
        return False

    return rec(0, full)


def is_counterexample(coloring):
    """Exact check: every 6-set of vertices induces all 5 colors,
    i.e. no color class has an independent 6-set."""
    masks = color_classes(coloring)
    return all(not max_independent_at_least(adj, 6) for adj in masks)


def violations(coloring, cap=None):
    """Count independent 6-sets per color (optionally stop early at cap).
    Exact but slow; for scoring candidates in searches."""
    masks = color_classes(coloring)
    total = 0
    for adj in masks:
        total += count_independent_6sets(adj, cap=None if cap is None else cap - total)
        if cap is not None and total >= cap:
            return total
    return total


def count_independent_6sets(adj, cap=None):
    cnt = 0
    full = (1 << N) - 1

    def rec(chosen, cand, lo):
        nonlocal cnt
        if cap is not None and cnt >= cap:
            return
        if chosen == 6:
            cnt += 1
            return
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            if v < lo:
                continue
            rec(chosen + 1, cand & ~adj[v] & ~((1 << (v + 1)) - 1), v + 1)
            if cap is not None and cnt >= cap:
                return

    rec(0, full, 0)
    return cnt


def verify_and_report(coloring):
    assert len(coloring) == 325 and all(0 <= c < R for c in coloring)
    masks = color_classes(coloring)
    sizes = [sum(bin(m).count("1") for m in adj) // 2 for adj in masks]
    bad = [c for c in range(R) if max_independent_at_least(masks[c], 6)]
    return {
        "edge_counts": sizes,
        "colors_with_independent_6set": bad,
        "is_counterexample": not bad,
    }
