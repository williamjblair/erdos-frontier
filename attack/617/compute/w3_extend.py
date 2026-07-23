"""Extension SAT: given a VALID K_25 coloring, can a 26th vertex be attached
(25 new edges, colors 0..4) so every 6-set of K_26 still sees all 5 colors?

New-vertex 6-sets are {w} + T for 5-subsets T of the 25 old vertices; the
constraint is: for every color c missing from T's 10 internal edges, some
edge w-t (t in T) gets color c.  125 vars, ~sum|M(T)| clauses.  Instant.

Usage:
  python3 w3_extend.py ag                 # test the AG(2,5) rook construction
  python3 w3_extend.py contract <best.txt> <u> <v>   # contract v into u, test
"""
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import core
from pysat.solvers import Cadical195

E25 = list(combinations(range(25), 2))
EIDX25 = {e: k for k, e in enumerate(E25)}


def ag_coloring():
    inv = [0, 1, 3, 2, 4]
    col = {}
    for u in range(25):
        for v in range(u + 1, 25):
            x1, y1, x2, y2 = u // 5, u % 5, v // 5, v % 5
            if x1 == x2 or y1 == y2:
                c = 0
            else:
                c = (((y2 - y1) % 5) * inv[(x2 - x1) % 5]) % 5
            col[EIDX25[(u, v)]] = c
    return [col[k] for k in range(len(E25))]


def contract(best_path, keep, drop):
    lines = open(best_path).read().split('\n')
    coloring = list(map(int, lines[1].split()))
    verts = [v for v in range(26) if v != drop]
    out = []
    for i in range(25):
        for j in range(i + 1, 25):
            u, v = verts[i], verts[j]
            out_k = EIDX25[(i, j)]
            assert out_k == len(out)
            out.append(coloring[core.edge_id(u, v)])
    return out


def check_valid_k25(col25):
    bad = 0
    for S in combinations(range(25), 6):
        cols = set(col25[EIDX25[e]] for e in combinations(S, 2))
        if len(cols) != 5:
            bad += 1
    return bad


def extension_sat(col25, verbose=True):
    var = lambda t, c: 5 * t + c + 1
    cls = []
    for t in range(25):
        cls.append([var(t, c) for c in range(5)])
        for c1 in range(5):
            for c2 in range(c1 + 1, 5):
                cls.append([-var(t, c1), -var(t, c2)])
    nc = 0
    for T in combinations(range(25), 5):
        present = set(col25[EIDX25[e]] for e in combinations(T, 2))
        for c in range(5):
            if c not in present:
                cls.append([var(t, c) for t in T])
                nc += 1
    t0 = time.time()
    with Cadical195(bootstrap_with=cls) as s:
        res = s.solve()
        dt = time.time() - t0
        if verbose:
            print(f'extension vars=125 clauses={len(cls)} (cover={nc}) '
                  f'-> {"SAT" if res else "UNSAT"} in {dt:.2f}s', flush=True)
        if res:
            model = set(l for l in s.get_model() if l > 0)
            attach = []
            for t in range(25):
                cs = [c for c in range(5) if var(t, c) in model]
                attach.append(cs[0])
            return attach
    return None


def build_k26(col25, attach):
    full = [0] * 325
    for (u, v), k in EIDX25.items():
        full[core.edge_id(u, v)] = col25[k]
    for t in range(25):
        full[core.edge_id(t, 25)] = attach[t]
    return full


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'ag':
        col25 = ag_coloring()
    else:
        col25 = contract(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]))
    bad = check_valid_k25(col25)
    print('K25 validity: bad 6-sets =', bad, flush=True)
    if bad:
        sys.exit('input K25 coloring invalid — extension test meaningless')
    attach = extension_sat(col25)
    if attach is not None:
        full = build_k26(col25, attach)
        rep = core.verify_and_report(full)
        print('core verification of extended K26:', rep, flush=True)
        if rep['is_counterexample']:
            import json
            out = '/Users/williamblair/personal/lean-proofs/compute617/witness.json'
            with open(out, 'w') as f:
                json.dump({'n': 26, 'r': 5, 'coloring': full,
                           'source': 'W3 extension ' + ' '.join(sys.argv[1:]),
                           'report': rep}, f)
            print('!!!! WITNESS FOUND (extension) — saved', out, '!!!!')
