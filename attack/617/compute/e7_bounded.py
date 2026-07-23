"""E7-BOUNDED: general n=26 instance + new cardinality bounds (P3).

Side lemmas (n=26 only — do NOT port to K_25 instances, where AG has six
edge-disjoint 5-clique covers):
  (i)  every class has >= 56 edges: complement K_6-free => class >= 325 -
       ex(26;K_6) = 325-270 = 55, and the unique 55-edge extremum is the
       {6,5,5,5,5} clique partition which contains K_6 — dead (E4 note).
  (ii) at most ONE class has a 5-clique-cover (E4 pigeonhole: any partition
       of 26 pts into <=5 cliques has a part of >=6 pts, which meets the <=5
       parts of any second such partition twice somewhere => shared edge —
       impossible for edge-disjoint classes).  A class WITHOUT a 5-clique-
       cover has non-5-partite K_6-free complement, so by Brouwer (1981,
       n >= 2r+1): e(complement) <= ex(26,5) - floor(26/5) + 1 = 266
       => class >= 59.  Hence >= 4 classes have >= 59 edges.
  (iii) consequently every class <= 325 - (3*59 + 56) = 92.

Encoding on top of the exact E7 base (fixing_sat identity: x(k,c) = 5k+c+1,
one-hot + 230230x5 coverage + color-break unit x(edge(0,1),0)):
  per class: atleast-56, atmost-92 (seqcounter);
  selectors a_c ("class c is one of the four guaranteed-fat classes"):
  pairwise (a_c OR a_d) [= at least 4 of 5 true] and conditionalized
  atleast-59 network (every clause ORed with -a_c).
Soundness of selectors for the UNSAT direction: any true counterexample has
>= 4 classes >= 59 (lemma ii); set those a_c true, the (at most one) other
false — all added clauses satisfiable.  SAT direction unchanged (witness is
still verified against core.py).

Usage: python3 e7_bounded.py selftest | dump | solve
"""
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import core
from pysat.card import CardEnc, EncType

NV_X = 325 * 5


def xvar(k, c):
    return 5 * k + c + 1


AVAR = [NV_X + 1 + c for c in range(5)]     # 1626..1630


def base_clauses():
    cls = []
    for k in range(325):
        cls.append([xvar(k, c) for c in range(5)])
        for c, d in combinations(range(5), 2):
            cls.append([-xvar(k, c), -xvar(k, d)])
    cls.append([xvar(0, 0)])                 # color relabel partial break
    for S in combinations(range(26), 6):
        ks = [core.edge_id(u, v) for u, v in combinations(S, 2)]
        for c in range(5):
            cls.append([xvar(k, c) for k in ks])
    return cls


def card_clauses(top=2000):
    """Returns (clauses, top).  Networks fresh-var-disjoint via top."""
    cls = []
    for c in range(5):
        lits = [xvar(k, c) for k in range(325)]
        enc = CardEnc.atleast(lits=lits, bound=56, top_id=top,
                              encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        top = max(top, enc.nv) + 10
        enc = CardEnc.atmost(lits=lits, bound=92, top_id=top,
                             encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        top = max(top, enc.nv) + 10
        enc = CardEnc.atleast(lits=lits, bound=59, top_id=top,
                              encoding=EncType.seqcounter)
        cls.extend([cl + [-AVAR[c]] for cl in enc.clauses])
        top = max(top, enc.nv) + 10
    for c, d in combinations(range(5), 2):   # at least 4 of 5 selectors
        cls.append([AVAR[c], AVAR[d]])
    return cls, top


def units_for_sizes(sizes):
    """Full pos+neg units for a coloring: first sizes[0] edges color 0, etc."""
    assert sum(sizes) == 325
    col, units = [], []
    for c, s in enumerate(sizes):
        col.extend([c] * s)
    for k in range(325):
        for c in range(5):
            units.append([xvar(k, c)] if col[k] == c else [-xvar(k, c)])
    return units


def selftest():
    from pysat.solvers import Kissat404
    cases = [((65, 65, 65, 65, 65), True),   # all fat
             ((58, 67, 67, 67, 66), True),   # one sub-59 allowed
             ((56, 58, 71, 70, 70), False),  # two sub-59: selector kill
             ((55, 68, 67, 67, 68), False),  # below floor 56
             ((93, 58, 58, 58, 58), False)]  # above cap 92 (also 3 sub-59)
    cc, _ = card_clauses()
    ok = True
    for sizes, expect in cases:
        with Kissat404(bootstrap_with=cc + units_for_sizes(sizes)) as s:
            sat = s.solve()
        good = sat == expect
        ok &= good
        print(f'  sizes {sizes}: {"SAT" if sat else "UNSAT"} '
              f'(expect {"SAT" if expect else "UNSAT"}) '
              f'{"OK" if good else "MISMATCH — BUG"}', flush=True)
    print('selftest', 'PASSED' if ok else 'FAILED', flush=True)
    return ok


def full():
    cls = base_clauses()
    cc, top = card_clauses()
    cls.extend(cc)
    return cls, top


def dump(path):
    cls, top = full()
    nv = max(top, NV_X + 5)
    t0 = time.time()
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(cls)}\n')
        for cl in cls:
            f.write(' '.join(map(str, cl)) + ' 0\n')
    print(f'dumped {path}: {nv} vars, {len(cls)} clauses '
          f'({time.time()-t0:.1f}s)', flush=True)


def solve():
    from pysat.solvers import Kissat404
    cls, _ = full()
    print(f'E7-BOUNDED: {len(cls)} clauses', flush=True)
    t0 = time.time()
    with Kissat404(bootstrap_with=cls) as s:
        sat = s.solve()
        print(f'E7-BOUNDED: {"SAT" if sat else "UNSAT"} in '
              f'{time.time()-t0:.1f}s', flush=True)
        if sat:
            model = set(l for l in s.get_model() if l > 0)
            coloring = [next(c for c in range(5) if xvar(k, c) in model)
                        for k in range(325)]
            rep = core.verify_and_report(coloring)
            print(rep, flush=True)
            if rep['is_counterexample']:
                import json
                with open('/Users/williamblair/personal/lean-proofs/'
                          'compute617/witness.json', 'w') as f:
                    json.dump({'family': 'E7-bounded', 'coloring': coloring,
                               'report': rep}, f)
                print('!!! VERIFIED COUNTEREXAMPLE — witness.json !!!',
                      flush=True)
        else:
            print('VERDICT: r=5 n=26 UNSAT modulo side lemmas (i)-(iii) '
                  'and encoder; keep unbounded E7 for the assumption-free '
                  'verdict; rerun standalone kissat + DRAT to certify.',
                  flush=True)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'selftest'
    if mode == 'selftest':
        selftest()
    elif mode == 'dump':
        dump('/Users/williamblair/personal/lean-proofs/compute617/runs/'
             'e7_bounded.cnf')
    elif mode == 'solve':
        if selftest():
            solve()
        else:
            print('ABORT: selftest failed, not solving', flush=True)
