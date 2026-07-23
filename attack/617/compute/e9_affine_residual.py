"""E9 — affine residual completion model (P0).

V = F_5^2 (vertex 5x+y) union {infty} (vertex 25).  The 300 plane edges fall
into 6 direction classes of 50 (slopes 0..4 and V=vertical, i.e. dx=0), each
class = 5 disjoint K_5s (the parallel lines).  MODEL: pick an omitted
direction d0; the 5 remaining directions ARE the 5 colors (any bijection is
WLOG by color symmetry); the 75 residual edges (50 of direction d0 + 25
infty-edges) are free.  Exact SAT on the completion: one-hot 5 per free edge
+ full coverage clause (6-set, color) over the induced 325-edge coloring,
clauses already covered by a fixed edge dropped.

Omitted-direction choice is WLOG under AGL(2,5): (x,y)->(y,x) swaps V and
slope 0 and inverts nonzero slopes; (x,y)->(x,x+y) shifts slopes by +1 fixing
V — together transitive on the 6 directions, and they permute direction
classes so they map model instances to model instances.  We still run ALL 6
omitted choices as belt and braces.

SAT => decode, verify against core.is_counterexample, save witness.json.
Note: omitted=V is exactly family E5, hand-proved empty in
constructions_log.md — this is the machine check of that proof.
"""
import json
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import core
from pysat.solvers import Kissat404

DIRS = ['V', 0, 1, 2, 3, 4]          # vertical (dx=0), slopes 0..4


def pt(v):
    return divmod(v, 5)               # vertex -> (x, y)


def direction(u, v):
    (x1, y1), (x2, y2) = pt(u), pt(v)
    dx, dy = (x2 - x1) % 5, (y2 - y1) % 5
    if dx == 0:
        return 'V'
    return (dy * pow(dx, 3, 5)) % 5   # dy/dx mod 5 (dx^3 = dx^-1 mod 5)


def build_instance(omit):
    """Return (fixed: eid->color, free: list of eid, dir_of_color note)."""
    kept = [d for d in DIRS if d != omit]           # 5 dirs -> colors 0..4
    dcol = {d: c for c, d in enumerate(kept)}
    fixed, free = {}, []
    for u, v in combinations(range(26), 2):
        eid = core.edge_id(u, v)
        if v == 25:                                  # infty edge
            free.append(eid)
            continue
        d = direction(u, v)
        if d == omit:
            free.append(eid)
        else:
            fixed[eid] = dcol[d]
    assert len(free) == 75 and len(fixed) == 250
    return fixed, free


def solve(omit):
    fixed, free = build_instance(omit)
    fidx = {e: i for i, e in enumerate(free)}
    x = lambda i, c: 5 * i + c + 1
    cls = []
    for i in range(75):
        cls.append([x(i, c) for c in range(5)])
        for c, d in combinations(range(5), 2):
            cls.append([-x(i, c), -x(i, d)])
    ncov = nskip = 0
    for S in combinations(range(26), 6):
        eids = [core.edge_id(u, v) for u, v in combinations(S, 2)]
        present = {fixed[e] for e in eids if e in fixed}
        frees = [fidx[e] for e in eids if e in fidx]
        for c in range(5):
            if c in present:
                nskip += 1
                continue
            if not frees:
                print(f'omit={omit}: EMPTY CLAUSE at S={S} c={c} '
                      f'=> UNSAT trivially', flush=True)
                return False
            cls.append([x(i, c) for i in frees])
            ncov += 1
    print(f'omit={omit}: {len(cls)} clauses ({ncov} coverage, '
          f'{nskip} pre-satisfied)', flush=True)
    t0 = time.time()
    with Kissat404(bootstrap_with=cls) as s:
        sat = s.solve()
        dt = time.time() - t0
        print(f'omit={omit}: {"SAT" if sat else "UNSAT"} in {dt:.1f}s',
              flush=True)
        if not sat:
            return False
        model = set(l for l in s.get_model() if l > 0)
        coloring = [None] * 325
        for e, c in fixed.items():
            coloring[e] = c
        for e, i in fidx.items():
            coloring[e] = next(c for c in range(5) if x(i, c) in model)
        rep = core.verify_and_report(coloring)
        print(f'omit={omit}: verify_and_report -> {rep}', flush=True)
        if rep['is_counterexample']:
            with open('/Users/williamblair/personal/lean-proofs/compute617/'
                      'witness.json', 'w') as f:
                json.dump({'family': 'E9 affine residual', 'omit': str(omit),
                           'coloring': coloring, 'report': rep}, f)
            print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!',
                  flush=True)
            print('!!! SAT WITNESS VERIFIED vs core.py — CONJECTURE '
                  'DISPROVED (r=5). saved witness.json !!!', flush=True)
            print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!',
                  flush=True)
            return True
        print(f'omit={omit}: SAT but FAILS core verification — ENCODER BUG, '
              f'investigate', flush=True)
        return True


def selftest():
    """Direction classes: 6 x 50 edges, each 5 disjoint K_5s."""
    from collections import Counter
    cnt = Counter(direction(u, v) for u, v in combinations(range(25), 2))
    assert all(cnt[d] == 50 for d in DIRS), cnt
    for d in DIRS:
        adj = {v: set() for v in range(25)}
        for u, v in combinations(range(25), 2):
            if direction(u, v) == d:
                adj[u].add(v), adj[v].add(u)
        comps = []
        seen = set()
        for v in range(25):
            if v in seen:
                continue
            stack, comp = [v], set()
            while stack:
                w = stack.pop()
                if w in comp:
                    continue
                comp.add(w)
                stack.extend(adj[w] - comp)
            seen |= comp
            comps.append(comp)
        assert len(comps) == 5 and all(len(c) == 5 for c in comps)
        for comp in comps:               # each component a K_5
            assert all(direction(a, b) == d for a, b in combinations(comp, 2))
    print('selftest OK: 6 direction classes x 50 edges, each 5 disjoint K_5s',
          flush=True)


if __name__ == '__main__':
    selftest()
    hit = False
    for omit in DIRS:
        hit |= bool(solve(omit))
    print('E9 OVERALL:', 'SAT SOMEWHERE — see above' if hit else
          'all 6 omitted-direction completions UNSAT — affine residual '
          'family EMPTY', flush=True)
