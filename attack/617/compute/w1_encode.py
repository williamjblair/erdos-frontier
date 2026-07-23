"""W1: full CNF encoding of Erdős #617 r=5 instance on K_n (default n=26).

Variables: x(k,c) = 5*k + c + 1 for edge index k in 0..NE-1 (lex order over
combinations(range(n),2), matching core.EDGES for n=26) and color c in 0..4.

Constraints:
  1. exactly-one color per edge (pairwise AMO).
  2. for every 6-set S and color c: OR_{e in S} x(e,c).
  3. color symmetry: colors appear in increasing first-occurrence order
     along the fixed edge enumeration (complete lex-leader for S_5 on colors).
  4. vertex symmetry: lex-leader constraints for the n-1 adjacent
     transpositions (i,i+1) acting on the color string (natural value order).
  5. cardinality: each color class has >= mn := C(n,2)-ex(n,K6) edges
     (complement of a class is K6-free) and <= C(n,2)-4*mn edges.

All constraints are sound lex-leader / counting facts: every valid coloring's
orbit under S_n x S_5 contains a representative satisfying all of them.
"""
import sys
from itertools import combinations

R = 5


def turan_min_edges(n):
    """min edges of graph on n vertices with alpha <= 5."""
    q, r = divmod(n, 5)
    parts = [q + 1] * r + [q] * (5 - r)
    ex = n * (n - 1) // 2 - sum(a * (a - 1) // 2 for a in parts)
    return n * (n - 1) // 2 - ex


def encode(n, with_card=True, with_vertex_lex=True):
    edges = list(combinations(range(n), 2))
    ne = len(edges)
    eidx = {e: k for k, e in enumerate(edges)}

    def x(k, c):
        return 5 * k + c + 1

    clauses = []
    top = 5 * ne

    # 1. exactly-one per edge
    for k in range(ne):
        clauses.append([x(k, c) for c in range(R)])
        for c1 in range(R):
            for c2 in range(c1 + 1, R):
                clauses.append([-x(k, c1), -x(k, c2)])

    # 2. 6-set coverage
    for S in combinations(range(n), 6):
        eids = [eidx[e] for e in combinations(S, 2)]
        for c in range(R):
            clauses.append([x(k, c) for k in eids])

    # 3. color symmetry via first-occurrence prefix vars
    p = {}
    for k in range(ne):
        for c in range(R):
            top += 1
            p[(k, c)] = top
    for k in range(ne):
        for c in range(R):
            cl = [-p[(k, c)], x(k, c)]
            if k > 0:
                cl.append(p[(k - 1, c)])
            clauses.append(cl)
    for k in range(ne):
        for c in range(1, R):
            if k == 0:
                clauses.append([-x(k, c)])
            else:
                clauses.append([-x(k, c), p[(k - 1, c - 1)]])

    # 4. vertex lex-leader for adjacent transpositions
    if with_vertex_lex:
        for i in range(n - 1):
            j = i + 1
            sigma = {}
            for u in range(n):
                if u == i or u == j:
                    continue
                k1 = eidx[tuple(sorted((u, i)))]
                k2 = eidx[tuple(sorted((u, j)))]
                sigma[k1] = k2
                sigma[k2] = k1
            pos = sorted(sigma)
            prev_a = None  # a_0 == True
            for t, k in enumerate(pos):
                kk = sigma[k]
                pre = [] if prev_a is None else [-prev_a]
                for va in range(R):
                    for vb in range(va):
                        clauses.append(pre + [-x(k, va), -x(kk, vb)])
                if t < len(pos) - 1:
                    top += 1
                    a_t = top
                    for c in range(R):
                        clauses.append(pre + [-x(k, c), -x(kk, c), a_t])
                    prev_a = a_t

    # 5. cardinality bounds per color
    if with_card:
        from pysat.card import CardEnc, EncType
        mn = turan_min_edges(n)
        mx = n * (n - 1) // 2 - 4 * mn
        if n == 26:
            # n=26 refinements (see sat_log.md 2026-07-10 P3; NOT valid for
            # n=25): (i) floor 56 — the 55-edge extremum is the {6,5,5,5,5}
            # clique partition, contains K_6, dead; (ii) at most one class
            # has a 5-clique cover (pigeonhole), others have non-5-partite
            # K_6-free complement <= 266 edges (Brouwer 1981) => >= 59, so
            # >= 4 classes >= 59; (iii) cap 325-(3*59+56) = 92.
            mn, mx = 56, 92
        for c in range(R):
            lits = [x(k, c) for k in range(ne)]
            enc = CardEnc.atleast(lits=lits, bound=mn, top_id=top,
                                  encoding=EncType.seqcounter)
            clauses.extend(enc.clauses)
            top = max(top, enc.nv)
            enc = CardEnc.atmost(lits=lits, bound=mx, top_id=top,
                                 encoding=EncType.seqcounter)
            clauses.extend(enc.clauses)
            top = max(top, enc.nv)
        if n == 26:
            # selectors a_c: at least 4 classes with >= 59 edges
            avars = []
            for c in range(R):
                top += 1
                avars.append(top)
            for c in range(R):
                lits = [x(k, c) for k in range(ne)]
                enc = CardEnc.atleast(lits=lits, bound=59, top_id=top,
                                      encoding=EncType.seqcounter)
                clauses.extend([cl + [-avars[c]] for cl in enc.clauses])
                top = max(top, enc.nv)
            for c1 in range(R):
                for c2 in range(c1 + 1, R):
                    clauses.append([avars[c1], avars[c2]])

    return top, clauses


def main(out_path, n):
    top, clauses = encode(n)
    with open(out_path, 'w') as f:
        f.write(f'p cnf {top} {len(clauses)}\n')
        for cl in clauses:
            f.write(' '.join(map(str, cl)) + ' 0\n')
    print(f'wrote {out_path} (n={n}): {top} vars, {len(clauses)} clauses')


if __name__ == '__main__':
    out = sys.argv[1]
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 26
    main(out, n)
