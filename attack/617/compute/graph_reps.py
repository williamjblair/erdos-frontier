"""Canonical representatives of graphs on m labeled vertices up to S_m,
their automorphism groups, and Aut-orbit-reduced cube deepening.

canon(m, mask) = min over pi in S_m of the relabeled edge-bitmask
(edges indexed by combinations(range(m),2) lex order).  Two graphs are
isomorphic iff equal canon.  Representative counts must match the known
sequence 1, 2, 4, 11, 34, 156, 1044, 12346 (graphs on 1..8 nodes).

CLI:  python3 graph_reps.py <m> <out.json>
writes [{'mask': int, 'edges': [[u,v],...], 'aut_size': int}, ...]
"""
import json
import sys
from itertools import combinations, permutations

import numpy as np


def edge_list(m):
    return list(combinations(range(m), 2))


def perm_edge_maps(m):
    """For each pi in S_m an array A with A[i] = index of pi(edge_i)."""
    el = edge_list(m)
    eidx = {e: i for i, e in enumerate(el)}
    maps = []
    for pi in permutations(range(m)):
        maps.append(np.array([eidx[tuple(sorted((pi[u], pi[v])))]
                              for u, v in el], dtype=np.int64))
    return np.array(maps)                       # (m!, C(m,2))


def canon_many(m, masks):
    """Vectorized canonical forms for an array of edge-bitmask ints."""
    ne = m * (m - 1) // 2
    pm = perm_edge_maps(m)                      # (P, ne)
    bits = ((masks[:, None] >> np.arange(ne)[None, :]) & 1)   # (N, ne)
    pw = (1 << np.arange(ne, dtype=np.int64))
    best = None
    for a in pm:
        # relabeled mask: bit j of new = bit at position where a==j …
        # equivalently new[:, a] = bits  → new_mask = sum bits * 2^a
        nm = bits @ pw[a]
        best = nm if best is None else np.minimum(best, nm)
    return best


def mask_from_edges(m, edges):
    el = edge_list(m)
    eidx = {e: i for i, e in enumerate(el)}
    mask = 0
    for e in edges:
        mask |= 1 << eidx[tuple(sorted(e))]
    return mask


def edges_from_mask(m, mask):
    el = edge_list(m)
    return [el[i] for i in range(len(el)) if (mask >> i) & 1]


def reps_correct(m):
    """Extension enumeration in the LEX edge indexing (edges (u,v) u<v of
    K_m in lex order — new-vertex edges are interleaved, so build masks via
    mask_from_edges on explicit edge lists)."""
    cur = [[]]                                   # m=1: no edges
    for k in range(2, m + 1):
        seen = {}
        cand_masks = []
        cand_edges = []
        for base_edges in cur:
            for nb in range(1 << (k - 1)):
                edges = list(base_edges) + [(u, k - 1)
                                            for u in range(k - 1)
                                            if (nb >> u) & 1]
                cand_edges.append(edges)
                cand_masks.append(mask_from_edges(k, edges))
        cand_masks = np.array(cand_masks, dtype=np.int64)
        cm = canon_many(k, cand_masks)
        uniq = np.unique(cm)
        cur = [edges_from_mask(k, int(u)) for u in uniq]
    return [mask_from_edges(m, e) for e in cur], cur


def aut_size_and_orbits(m, mask, subset_universe=None):
    """|Aut(G)| and orbit representatives of subsets of {0..m-1} under Aut.
    subset_universe: iterable of subset bitmasks; default all 2^m."""
    el = edge_list(m)
    ne = len(el)
    eidx = {e: i for i, e in enumerate(el)}
    auts = []
    for pi in permutations(range(m)):
        nm = 0
        ok = True
        for i in range(ne):
            if (mask >> i) & 1:
                u, v = el[i]
                nm |= 1 << eidx[tuple(sorted((pi[u], pi[v])))]
        if nm == mask:
            auts.append(pi)
    universe = subset_universe if subset_universe is not None \
        else range(1 << m)
    orbit_reps = []
    seen = set()
    for s in universe:
        if s in seen:
            continue
        orb = set()
        for pi in auts:
            t = 0
            for v in range(m):
                if (s >> v) & 1:
                    t |= 1 << pi[v]
            orb.add(t)
        seen |= orb
        orbit_reps.append(min(orb))
    return len(auts), orbit_reps


def main():
    m = int(sys.argv[1])
    out = sys.argv[2]
    known = {1: 1, 2: 2, 3: 4, 4: 11, 5: 34, 6: 156, 7: 1044, 8: 12346}
    masks, edge_lists = reps_correct(m)
    assert len(masks) == known[m], (len(masks), known[m])
    recs = []
    for mask, edges in zip(masks, edge_lists):
        a, _ = aut_size_and_orbits(m, mask, subset_universe=[0])
        recs.append({'mask': int(mask), 'edges': [list(e) for e in edges],
                     'aut_size': a})
    with open(out, 'w') as f:
        json.dump(recs, f)
    print(f'{len(recs)} reps on {m} vertices -> {out} '
          f'(matches known count {known[m]})')


if __name__ == '__main__':
    main()
