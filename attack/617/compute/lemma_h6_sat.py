"""TARGET LEMMA SAT: does there exist a valid K_25 coloring (5 colors,
every 6-set sees all 5 colors) together with a set H of <= B vertices such
that, for class 0 (WLOG by color symmetry),
  (i)  H hits every independent 5-set of G_0, and
  (ii) H contains no 5-clique of G_0 ?

If UNSAT for B = 5: every class of every valid K_25 coloring has h_c >= 6,
hence sum_c h_c >= 30 > 25, hence NO valid K_25 is 1-vertex-extendable,
hence (since a valid K_26 restricted to any 25 vertices is a valid,
extendable K_25) the r=5, n=26 instance of Erdos #617 has NO counterexample.
This settles the case independently of the E7 general instance.

Encoding:
  x_{k,c} (k=0..299 edge of K_25, c=0..4): var 5k+c+1   (one-hot per edge)
  H_t (t=0..24): var 1501+t
  validity: for every 6-set S, every color c: OR_{e in S} x_{e,c}
  (i): for every 5-set T: OR_{e in T} x_{e,0}  OR  OR_{t in T} H_t
       (if no internal edge has color 0, T is independent in G_0 -> H hits T)
  (ii): for every 5-set T: OR_{e in T} -x_{e,0} OR OR_{t in T} -H_t
       (not all 10 edges color 0 while all 5 vertices are in H)
  card: sum H_t <= B (seqcounter)

Usage:
  python3 lemma_h6_sat.py selftest <best.txt>   # fixed coloring: SAT iff B>=h
  python3 lemma_h6_sat.py solve <B>             # the lemma instance
"""
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from pysat.card import CardEnc, EncType
from pysat.solvers import Kissat404

E25 = list(combinations(range(25), 2))
EIDX25 = {e: k for k, e in enumerate(E25)}
NV_X = 1500


def xvar(k, c):
    return 5 * k + c + 1


def hvar(t):
    return NV_X + 1 + t


def build(bound):
    cls = []
    for k in range(300):
        cls.append([xvar(k, c) for c in range(5)])
        for c, d in combinations(range(5), 2):
            cls.append([-xvar(k, c), -xvar(k, d)])
    for S in combinations(range(25), 6):
        ks = [EIDX25[e] for e in combinations(S, 2)]
        for c in range(5):
            cls.append([xvar(k, c) for k in ks])
    for T in combinations(range(25), 5):
        ks = [EIDX25[e] for e in combinations(T, 2)]
        cls.append([xvar(k, 0) for k in ks] + [hvar(t) for t in T])
        cls.append([-xvar(k, 0) for k in ks] + [-hvar(t) for t in T])
    enc = CardEnc.atmost(lits=[hvar(t) for t in range(25)], bound=bound,
                         top_id=NV_X + 100, encoding=EncType.seqcounter)
    cls.extend(enc.clauses)
    return cls


def solve(cls, tag):
    t0 = time.time()
    with Kissat404(bootstrap_with=cls) as s:
        sat = s.solve()
        dt = time.time() - t0
        print(f'{tag}: {"SAT" if sat else "UNSAT"} in {dt:.1f}s', flush=True)
        if sat:
            model = set(l for l in s.get_model() if l > 0)
            col = [[c for c in range(5) if xvar(k, c) in model][0]
                   for k in range(300)]
            H = [t for t in range(25) if hvar(t) in model]
            return col, H
    return None


def main():
    mode = sys.argv[1]
    if mode == 'selftest':
        path = sys.argv[2]
        lines = open(path).read().split('\n')
        assert int(lines[0]) == 0, 'not a valid K25 best file'
        col = list(map(int, lines[1].split()))
        units = [[xvar(k, col[k])] for k in range(300)]
        # h for class 0 of this coloring is known via w3_certificate;
        # check SAT/UNSAT flips at the right bound.
        from w3_certificate import class_graph, min_admissible_hitting_set
        adj = class_graph(col, 0)
        h, ni, ncl, _ = min_admissible_hitting_set(adj)
        print(f'reference h_0 = {h} (ind5={ni} cl5={ncl})', flush=True)
        for b in (h - 1, h):
            cls = build(b) + units
            r = solve(cls, f'selftest B={b} (expect '
                           f'{"UNSAT" if b < h else "SAT"})')
            ok = (r is None) == (b < h)
            print(f'  -> {"OK" if ok else "MISMATCH — ENCODER BUG"}',
                  flush=True)
    else:
        bound = int(sys.argv[2])
        t0 = time.time()
        cls = build(bound)
        print(f'lemma instance B={bound}: {len(cls)} clauses '
              f'({time.time()-t0:.1f}s)', flush=True)
        r = solve(cls, f'LEMMA h<= {bound}')
        if r is None:
            print(f'VERDICT: every class of every valid K_25 has h_c > '
                  f'{bound}.', flush=True)
            if bound >= 5:
                print('*** sum h_c >= 5*6=30 > 25 for EVERY valid K_25: no '
                      'valid K_25 is extendable => r=5 n=26 has NO '
                      'counterexample (modulo encoder). ***', flush=True)
        else:
            col, H = r
            print('SAT witness found: class 0 admits |H| <=', bound,
                  'H =', H, flush=True)
            print('coloring:', ' '.join(map(str, col)), flush=True)
            print('>>> compute full h vector + attempt extension NOW '
                  '(harvest.py machinery). <<<', flush=True)


if __name__ == '__main__':
    main()
