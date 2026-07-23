"""Decomposed counting-lemma SAT instances over valid K_25 colorings.

Modes (all: 5-coloring of E(K_25), every 6-set sees all 5 colors):
  edges <E>  : class 0 admits admissible H with |H| <= 5 AND |E_0| <= E.
               UNSAT for E=75 => any class with h<=5 has >= 76 edges =>
               (edge budget 300, floor 50) at most ONE cheap class.
  floor <B>  : class 0 admits admissible H with |H| <= B (B=1: UNSAT =>
               h_c >= 2 for every class of every valid K_25).
  sum        : H_0..H_4, each admissible for its class, sum |H_c| <= 25.
               UNSAT => sum_c h_c > 25 for EVERY valid K_25 => no valid
               K_25 is 1-vertex-extendable => r=5 n=26 settled (UNSAT).

Combination edges(75)+floor(1) also settles it:
  at most one cheap class, cheap one h>=2, others h>=6 => sum >= 26 > 25.

Admissible H for class c: hits every independent 5-set of G_c, contains no
5-clique of G_c (both encoded per 5-set, conditionally on edge colors).
"""
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Kissat404

E25 = list(combinations(range(25), 2))
EIDX25 = {e: k for k, e in enumerate(E25)}


def xvar(k, c):
    return 5 * k + c + 1


def base_validity():
    cls = []
    for k in range(300):
        cls.append([xvar(k, c) for c in range(5)])
        for c, d in combinations(range(5), 2):
            cls.append([-xvar(k, c), -xvar(k, d)])
    for S in combinations(range(25), 6):
        ks = [EIDX25[e] for e in combinations(S, 2)]
        for c in range(5):
            cls.append([xvar(k, c) for k in ks])
    return cls


def admissibility(cls, hv, c):
    """hv: function t -> literal for 'vertex t in H_c'."""
    for T in combinations(range(25), 5):
        ks = [EIDX25[e] for e in combinations(T, 2)]
        cls.append([xvar(k, c) for k in ks] + [hv(t) for t in T])
        cls.append([-xvar(k, c) for k in ks] + [-hv(t) for t in T])


def run(cls, tag):
    print(f'{tag}: {len(cls)} clauses', flush=True)
    t0 = time.time()
    with Kissat404(bootstrap_with=cls) as s:
        sat = s.solve()
        print(f'{tag}: {"SAT" if sat else "UNSAT"} in {time.time()-t0:.1f}s',
              flush=True)
        if sat:
            model = set(l for l in s.get_model() if l > 0)
            col = [[c for c in range(5) if xvar(k, c) in model][0]
                   for k in range(300)]
            print('coloring:', ' '.join(map(str, col)), flush=True)
            return model
    return None


def main():
    mode = sys.argv[1]
    top = 2000
    cls = base_validity()
    if mode == 'edges':
        ebound = int(sys.argv[2])
        hv = lambda t: 1501 + t
        admissibility(cls, hv, 0)
        enc = CardEnc.atmost(lits=[hv(t) for t in range(25)], bound=5,
                             top_id=top, encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        top = max(top, enc.nv)
        enc2 = CardEnc.atmost(lits=[xvar(k, 0) for k in range(300)],
                              bound=ebound, top_id=top + 10,
                              encoding=EncType.seqcounter)
        cls.extend(enc2.clauses)
        m = run(cls, f'LEMMA-A cheap class with <= {ebound} edges')
        if m is None:
            print(f'VERDICT: any class with h<=5 has >= {ebound+1} edges; '
                  f'if {ebound+1} >= 76, at most one cheap class per valid '
                  f'K_25.', flush=True)
    elif mode == 'floor':
        b = int(sys.argv[2])
        hv = lambda t: 1501 + t
        admissibility(cls, hv, 0)
        enc = CardEnc.atmost(lits=[hv(t) for t in range(25)], bound=b,
                             top_id=top, encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        m = run(cls, f'LEMMA-B h <= {b}')
        if m is None:
            print(f'VERDICT: h_c >= {b+1} for every class of every valid '
                  f'K_25.', flush=True)
    elif mode == 'sum':
        pool = IDPool(start_from=1501)
        hvs = [[pool.id(('H', c, t)) for t in range(25)] for c in range(5)]
        for c in range(5):
            admissibility(cls, lambda t, c=c: hvs[c][t], c)
        allh = [hvs[c][t] for c in range(5) for t in range(25)]
        enc = CardEnc.atmost(lits=allh, bound=25, top_id=pool.top + 10,
                             encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        m = run(cls, 'LEMMA-SUM sum|H_c| <= 25')
        if m is None:
            print('*** VERDICT: sum_c h_c > 25 for EVERY valid K_25 => no '
                  'valid K_25 extendable => r=5 n=26 UNSAT (modulo encoder) '
                  '***', flush=True)
        else:
            print('sum <= 25 achieved — EXTENSION ATTEMPT REQUIRED (check '
                  'H sets, then E7-style completion).', flush=True)


if __name__ == '__main__':
    main()
