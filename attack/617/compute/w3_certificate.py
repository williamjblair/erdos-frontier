"""Counting certificate for non-extendability of a valid K_25 coloring.

For an attached vertex w and color c, let H_c = N_c(w) (subset of the 25 old
vertices).  Necessary conditions for the extended coloring to be valid:
  (i)  H_c hits every independent 5-set of G_c  (else that 5-set + w is an
       independent 6-set of G_c);
  (ii) H_c contains no 5-clique of G_c  (else 5-clique + w is a mono K_6,
       which is an independent 6-set in every other class);
  (iii) the H_c partition the 25 old vertices (each edge w-t has one color),
        so sum_c |H_c| = 25.

Let h_c = min{|H| : H satisfies (i) and (ii) for class c}.
If sum_c h_c > 25, no extension exists — a counting certificate.

Usage: python3 w3_certificate.py ag
       python3 w3_certificate.py contract <best.txt> <keep> <drop>
"""
import sys
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from pysat.solvers import Cadical195
from pysat.card import CardEnc, EncType
from w3_extend import ag_coloring, contract, check_valid_k25, E25, EIDX25


def class_graph(col25, c):
    adj = [0] * 25
    for (u, v), k in EIDX25.items():
        if col25[k] == c:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    return adj


def enum_independent_5sets(adj):
    out = []
    def rec(cand, lo, cur):
        if len(cur) == 5:
            out.append(tuple(cur))
            return
        c2 = cand
        while c2:
            v = (c2 & -c2).bit_length() - 1
            c2 &= c2 - 1
            cur.append(v)
            rec(cand & ~adj[v] & ~((1 << (v + 1)) - 1), v + 1, cur)
            cur.pop()
    rec((1 << 25) - 1, 0, [])
    return out


def enum_5cliques(adj):
    out = []
    def rec(cand, cur):
        if len(cur) == 5:
            out.append(tuple(cur))
            return
        c2 = cand
        while c2:
            v = (c2 & -c2).bit_length() - 1
            c2 &= c2 - 1
            cur.append(v)
            rec(cand & adj[v] & ~((1 << (v + 1)) - 1), cur)
            cur.pop()
    rec((1 << 25) - 1, [])
    return out


def min_admissible_hitting_set(adj, ub=25):
    """binary search min |H|: H hits all independent 5-sets, contains no
    5-clique of adj.  Returns (h, witness_H or None at h-1 infeasible)."""
    ind5 = enum_independent_5sets(adj)
    cl5 = enum_5cliques(adj)
    base = []
    for T in ind5:
        base.append([t + 1 for t in T])          # var v+1 = "v in H"
    for K in cl5:
        base.append([-(v + 1) for v in K])
    # feasibility check without cardinality bound: does ANY admissible H exist?
    with Cadical195(bootstrap_with=base) as s:
        if not s.solve():
            return 999, len(ind5), len(cl5), None  # infeasible: h_c = infinity
    lo, hi = 0, ub  # find min k s.t. feasible with |H| <= k
    best = None
    while lo < hi:
        mid = (lo + hi) // 2
        cnf = list(base)
        enc = CardEnc.atmost(lits=list(range(1, 26)), bound=mid,
                             top_id=100, encoding=EncType.seqcounter)
        cnf.extend(enc.clauses)
        with Cadical195(bootstrap_with=cnf) as s:
            if s.solve():
                best = [v - 1 for v in range(1, 26)
                        if v in set(l for l in s.get_model() if l > 0)]
                hi = mid
            else:
                lo = mid + 1
    return lo, len(ind5), len(cl5), best


def main():
    mode = sys.argv[1]
    if mode == 'ag':
        col25 = ag_coloring()
        tag = 'ag'
    else:
        col25 = contract(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
        tag = f'{sys.argv[2]}~{sys.argv[3]}/{sys.argv[4]}'
    assert check_valid_k25(col25) == 0, 'invalid K25 input'
    total = 0
    sizes = [sum(1 for k in range(300) if col25[k] == c) for c in range(5)]
    print(f'[{tag}] class sizes: {sizes}')
    for c in range(5):
        adj = class_graph(col25, c)
        h, ni, nc, H = min_admissible_hitting_set(adj)
        total += h
        print(f'  class {c}: edges={sizes[c]} ind5sets={ni} 5cliques={nc} '
              f'h_c={h}', flush=True)
    verdict = 'NON-EXTENDABLE (counting certificate)' if total > 25 else \
              'no counting obstruction (sum <= 25)'
    print(f'  sum h_c = {total}  -> {verdict}')


if __name__ == '__main__':
    main()
