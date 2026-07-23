"""Silence-aware lemma/cube instances over valid K_25 colorings.

A class c is SILENT if alpha(G_c) <= 4 (no independent 5-set): its
extension demand is h_c = 0, so the naive per-class lemmas must condition
on LOUDNESS (alpha = 5 exactly, i.e. some independent 5-set exists).

Hand-proved cube bounds (banked in sat_log.md):
  silent class => >= 67 edges (66 forces complement = Turan K_{7,6,6,6},
  i.e. G = K_7+K_6+K_6+K_6, which contains K_6 — forbidden in any class);
  loud class => >= 50 edges (5xK_5 achieves).  3*67 + 2*50 = 301 > 300
  => at most s <= 2 silent classes.

Modes:
  silent        : valid K_25 + class 0 SILENT.  UNSAT kills cubes s=1,2.
  double_silent : valid K_25 + classes 0,1 SILENT.  UNSAT kills cube s=2.
                  (s=2 is the danger cube: 2 silent + 3 loud at h=8 gives
                  sum h = 24 <= 25 — the only region where the counting
                  certificate would not block extension.)
  floor_loud B  : valid + class 0 LOUD + admissible H, |H| <= B.
                  UNSAT at B=1 => every loud class has h >= 2.
  edges_loud B E: valid + class 0 LOUD + admissible H, |H| <= B,
                  |E_0| <= E.  UNSAT at (5,75) => cheap loud class needs
                  >= 76 edges => at most one cheap loud class (s=0 leg).
  selftest      : encoder property tests (fixed colorings, known answers).

Loudness encoding: aux y_T ("T is the loudness witness"), one clause
OR_T y_T, and y_T -> edge e not colored 0 for each of T's 10 edges.
Silence encoding: for every 5-set T: OR_{e in T} x_{e,c}.

Vars: x 1..1500, H 1501..1525, y 1526..55155(?), card aux from 60000.
"""
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from pysat.card import CardEnc, EncType
from pysat.solvers import Kissat404

E25 = list(combinations(range(25), 2))
EIDX25 = {e: k for k, e in enumerate(E25)}
FIVESETS = list(combinations(range(25), 5))


def xvar(k, c):
    return 5 * k + c + 1


def hvar(t):
    return 1501 + t


def yvar(i):
    return 1526 + i


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


def silence(cls, c):
    for T in FIVESETS:
        cls.append([xvar(EIDX25[e], c) for e in combinations(T, 2)])


def loudness(cls, c):
    big = []
    for i, T in enumerate(FIVESETS):
        big.append(yvar(i))
        for e in combinations(T, 2):
            cls.append([-yvar(i), -xvar(EIDX25[e], c)])
    cls.append(big)


def admissibility(cls, c):
    for T in FIVESETS:
        ks = [EIDX25[e] for e in combinations(T, 2)]
        cls.append([xvar(k, c) for k in ks] + [hvar(t) for t in T])
        cls.append([-xvar(k, c) for k in ks] + [-hvar(t) for t in T])


def hcard(cls, bound):
    enc = CardEnc.atmost(lits=[hvar(t) for t in range(25)], bound=bound,
                         top_id=60000, encoding=EncType.seqcounter)
    cls.extend(enc.clauses)
    return max(60000, enc.nv)


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
            return col
    return None


def main():
    mode = sys.argv[1]
    if mode == 'silent':
        cls = base_validity()
        silence(cls, 0)
        col = run(cls, 'SILENT-EXISTS (valid K25 with an alpha<=4 class)')
        if col is None:
            print('VERDICT: no valid K_25 has a silent class => cubes '
                  's=1,2 are EMPTY; only s=0 remains.', flush=True)
        else:
            print('silent-class valid K25 EXISTS — cube s=1,2 live; '
                  'run double_silent and s=1 demand instances.', flush=True)
    elif mode == 'double_silent':
        cls = base_validity()
        silence(cls, 0)
        silence(cls, 1)
        col = run(cls, 'DOUBLE-SILENT (valid K25, two alpha<=4 classes)')
        if col is None:
            print('VERDICT: cube s=2 is EMPTY.', flush=True)
        else:
            print('!!! DANGER CUBE INHABITED: sum h can be 24 <= 25 here. '
                  'Compute h vector + extension SAT on this witness NOW.',
                  flush=True)
    elif mode == 'floor_loud':
        b = int(sys.argv[2])
        cls = base_validity()
        loudness(cls, 0)
        admissibility(cls, 0)
        hcard(cls, b)
        col = run(cls, f'FLOOR-LOUD h<={b} (class 0 loud)')
        if col is None:
            print(f'VERDICT: every LOUD class of every valid K_25 has '
                  f'h >= {b+1}.', flush=True)
    elif mode == 'edges_loud':
        b = int(sys.argv[2])
        ebound = int(sys.argv[3])
        cls = base_validity()
        loudness(cls, 0)
        admissibility(cls, 0)
        top = hcard(cls, b)
        enc = CardEnc.atmost(lits=[xvar(k, 0) for k in range(300)],
                             bound=ebound, top_id=top + 10,
                             encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        col = run(cls, f'EDGES-LOUD h<={b} |E0|<={ebound}')
        if col is None:
            print(f'VERDICT: a loud class with h <= {b} has >= {ebound+1} '
                  f'edges.', flush=True)
    elif mode == 'sum_silent':
        # s=1 joint cube: class 0 SILENT (h_0 = 0, H_0 = empty) + admissible
        # H_1..H_4 with sum <= 25.  UNSAT => in cube s=1 the counting
        # certificate blocks extension (sum h > 25).  Complements LEMMA-SUM
        # (which covers all cubes at once but is one big instance).
        from pysat.formula import IDPool
        cls = base_validity()
        silence(cls, 0)
        pool = IDPool(start_from=60000)
        hvs = {c: [pool.id(('H', c, t)) for t in range(25)]
               for c in range(1, 5)}
        for c in range(1, 5):
            for T in FIVESETS:
                ks = [EIDX25[e] for e in combinations(T, 2)]
                cls.append([xvar(k, c) for k in ks] +
                           [hvs[c][t] for t in T])
                cls.append([-xvar(k, c) for k in ks] +
                           [-hvs[c][t] for t in T])
        allh = [hvs[c][t] for c in range(1, 5) for t in range(25)]
        enc = CardEnc.atmost(lits=allh, bound=25, top_id=pool.top + 10,
                             encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        col = run(cls, 'SUM-SILENT (class 0 silent, sum_{c>=1}|H_c| <= 25)')
        if col is None:
            print('VERDICT: cube s=1 closed — silent class forces '
                  'sum h_c > 25 on the loud classes.', flush=True)
        else:
            print('sum <= 25 with a silent class — EXTENSION ATTEMPT '
                  'REQUIRED on this witness.', flush=True)
    elif mode == 'selftest':
        # (1) fixed h=5 loud witness: floor_loud flips at B=5
        lines = open('runs25/hclimb_ag.best.txt').read().split('\n')
        col = list(map(int, lines[1].split()))
        units = [[xvar(k, col[k])] for k in range(300)]
        for b, expect in ((4, False), (5, True)):
            cls = base_validity()
            loudness(cls, 0)
            admissibility(cls, 0)
            hcard(cls, b)
            r = run(cls + units, f'selftest floor_loud B={b}')
            print('  ->', 'OK' if (r is not None) == expect else
                  'MISMATCH — BUG', flush=True)
        # (2) all-color-0 coloring: class 0 has alpha=1 (silent);
        # silence clauses must be SAT, loudness clauses must be UNSAT.
        units0 = [[xvar(k, 0)] for k in range(300)]
        cls = []
        silence(cls, 0)
        r = run(cls + units0, 'selftest silence on K25 all-0')
        print('  ->', 'OK' if r is not None else 'MISMATCH — BUG', flush=True)
        cls = []
        loudness(cls, 0)
        r = run(cls + units0, 'selftest loudness on K25 all-0')
        print('  ->', 'OK' if r is None else 'MISMATCH — BUG', flush=True)
        # (3) AG fixed: class 0 (rook) is loud -> loudness SAT
        from w3_extend import ag_coloring
        ag = ag_coloring()
        unitsag = [[xvar(k, ag[k])] for k in range(300)]
        cls = []
        loudness(cls, 0)
        r = run(cls + unitsag, 'selftest loudness on AG rook class')
        print('  ->', 'OK' if r is not None else 'MISMATCH — BUG', flush=True)
        # (4) AG fixed with FULL units (pos+neg — silence clauses read
        # x_{e,0} of non-class-0 edges, which pos units alone leave free):
        # silence of the rook class must fail (alpha(rook)=5, loud).
        unitsag_full = []
        for k in range(300):
            for c in range(5):
                unitsag_full.append([xvar(k, c) if ag[k] == c
                                     else -xvar(k, c)])
        cls = []
        silence(cls, 0)
        r = run(cls + unitsag_full, 'selftest silence on AG rook class')
        print('  ->', 'OK' if r is None else 'MISMATCH — BUG', flush=True)


if __name__ == '__main__':
    main()
