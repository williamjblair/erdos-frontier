"""W1 solver: load DIMACS, run CaDiCaL 1.9.5 (pysat), decode + verify.

Usage: python3 w1_solve.py <cnf_path> <n>
"""
import json
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from pysat.formula import CNF
from pysat.solvers import Cadical195


def decode(model, ne):
    pos = set(l for l in model if l > 0)
    coloring = []
    for k in range(ne):
        cs = [c for c in range(5) if 5 * k + c + 1 in pos]
        assert len(cs) == 1, (k, cs)
        coloring.append(cs[0])
    return coloring


def check_all_6sets(coloring, n):
    """independent verification: every 6-set sees all 5 colors."""
    eidx = {e: k for k, e in enumerate(combinations(range(n), 2))}
    bad = 0
    for S in combinations(range(n), 6):
        cols = set(coloring[eidx[e]] for e in combinations(S, 2))
        if len(cols) != 5:
            bad += 1
    return bad


def main(cnf_path, n):
    ne = n * (n - 1) // 2
    t0 = time.time()
    cnf = CNF(from_file=cnf_path)
    print(f'loaded {cnf_path} (n={n}): {cnf.nv} vars {len(cnf.clauses)} clauses '
          f'({time.time()-t0:.0f}s)', flush=True)
    with Cadical195(bootstrap_with=cnf) as s:
        res = s.solve()
        dt = time.time() - t0
        print(f'result={res} time={dt:.0f}s', flush=True)
        if res:
            coloring = decode(s.get_model(), ne)
            bad = check_all_6sets(coloring, n)
            print(f'independent 6-set recheck: {bad} bad 6-sets', flush=True)
            if n == 26:
                import core
                rep = core.verify_and_report(coloring)
                print('core.verify_and_report:', rep, flush=True)
                if rep['is_counterexample']:
                    out = ('/Users/williamblair/personal/lean-proofs/'
                           'compute617/witness.json')
                    with open(out, 'w') as f:
                        json.dump({'n': 26, 'r': 5, 'coloring': coloring,
                                   'source': 'W1 SAT ' + cnf_path,
                                   'report': rep}, f)
                    print('!!!! WITNESS FOUND (SAT) — saved', out, '!!!!',
                          flush=True)
                else:
                    print('ERROR: SAT model fails core verification — '
                          'encoding bug!', flush=True)
        else:
            print('UNSAT for the symmetry-broken instance; constraints are '
                  'sound, so the base instance is UNSAT too (modulo encoder '
                  'correctness).', flush=True)


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]))
