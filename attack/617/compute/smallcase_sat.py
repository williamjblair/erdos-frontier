"""General (unrestricted) SAT for the small analogues: r colors on K_{r^2+1},
every (r+1)-set must contain all r colors.  Symmetry: fix color(0,1)=0.
Usage: python3 smallcase_sat.py <r>"""
import sys, time
from itertools import combinations
from pysat.solvers import Kissat404

r = int(sys.argv[1])
n = r * r + 1
edges = list(combinations(range(n), 2))
eidx = {e: k for k, e in enumerate(edges)}

def var(k, c):
    return k * r + c + 1

clauses = [[var(0, 0)]]
for k in range(len(edges)):
    clauses.append([var(k, c) for c in range(r)])
    for c, d in combinations(range(r), 2):
        clauses.append([-var(k, c), -var(k, d)])
for S in combinations(range(n), r + 1):
    ks = [eidx[p] for p in combinations(S, 2)]
    for c in range(r):
        clauses.append([var(k, c) for k in ks])
print(f"r={r} K_{n}: {len(clauses)} clauses", flush=True)
t0 = time.time()
with Kissat404(bootstrap_with=clauses) as s:
    sat = s.solve()
    model = s.get_model() if sat else None
print(f"r={r} K_{n} GENERAL: {'SAT' if sat else 'UNSAT'} ({time.time()-t0:.1f}s)", flush=True)
if sat:
    pos = set(l for l in model if l > 0)
    col = [[c for c in range(r) if var(k, c) in pos][0] for k in range(len(edges))]
    print("coloring:", "".join(map(str, col)))
