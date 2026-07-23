"""W3: completion SAT. Freeze a partial coloring, free all edges incident to
a vertex set F, ask CaDiCaL whether the free edges can be recolored so every
6-set sees all 5 colors.  If SAT -> full counterexample (verified vs core).

Usage: python3 w3_completion.py <best.txt> <v1,v2,...> [timeout_ignored]
"""
import json
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import core
from pysat.solvers import Cadical195


def main(best_path, free_verts):
    lines = open(best_path).read().split('\n')
    coloring = list(map(int, lines[1].split())) if len(lines) > 1 and lines[1] \
        else list(map(int, lines[0].split()))
    assert len(coloring) == 325
    F = set(free_verts)
    free_edges = [k for k, (u, v) in enumerate(core.EDGES)
                  if u in F or v in F]
    fset = set(free_edges)
    var = {}
    nv = 0
    for k in free_edges:
        for c in range(5):
            nv += 1
            var[(k, c)] = nv

    cls = []
    for k in free_edges:
        cls.append([var[(k, c)] for c in range(5)])
        for c1 in range(5):
            for c2 in range(c1 + 1, 5):
                cls.append([-var[(k, c1)], -var[(k, c2)]])

    nconstraints = 0
    for S in combinations(range(26), 6):
        if not (F & set(S)):
            continue
        eids = [core.edge_id(u, v) for u, v in combinations(S, 2)]
        fixed_cols = set(coloring[k] for k in eids if k not in fset)
        free_here = [k for k in eids if k in fset]
        for c in range(5):
            if c in fixed_cols:
                continue
            if not free_here:
                print('UNSAT trivially: 6-set', S, 'missing color', c,
                      'with no free edge')
                return
            cls.append([var[(k, c)] for k in free_here])
            nconstraints += 1

    print(f'F={sorted(F)}: {len(free_edges)} free edges, {nv} vars, '
          f'{len(cls)} clauses ({nconstraints} coverage)', flush=True)
    t0 = time.time()
    with Cadical195(bootstrap_with=cls) as s:
        res = s.solve()
        print(f'result={res} time={time.time()-t0:.1f}s', flush=True)
        if res:
            model = set(l for l in s.get_model() if l > 0)
            new = list(coloring)
            for k in free_edges:
                cs = [c for c in range(5) if var[(k, c)] in model]
                assert len(cs) == 1
                new[k] = cs[0]
            rep = core.verify_and_report(new)
            print('core.verify_and_report:', rep, flush=True)
            if rep['is_counterexample']:
                out = ('/Users/williamblair/personal/lean-proofs/compute617/'
                       'witness.json')
                with open(out, 'w') as f:
                    json.dump({'n': 26, 'r': 5, 'coloring': new,
                               'source': f'W3 completion {best_path} F={sorted(F)}',
                               'report': rep}, f)
                print('!!!! WITNESS FOUND (W3) — saved', out, '!!!!', flush=True)


if __name__ == '__main__':
    main(sys.argv[1], [int(x) for x in sys.argv[2].split(',')])
