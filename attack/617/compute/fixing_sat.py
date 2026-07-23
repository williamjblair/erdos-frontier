"""Generic orbit-fixing SAT: coloring constant on edge-orbits of permutation pi
(given by cycle type over 26 vertices, parts listed incl. 1s).  Clauses: every
6-set contains an edge of every color (exact statement of is_counterexample).
Usage: python3 fixing_sat.py 24,1,1
"""
import json, sys, time
from itertools import combinations

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute617")
import core

parts = [int(x) for x in sys.argv[1].split(",")]
assert sum(parts) == 26
tag = "-".join(map(str, parts))

perm = list(range(26))
s = 0
for p in parts:
    for i in range(p):
        perm[s + i] = s + (i + 1) % p
    s += p


def pi_edge(e):
    u, v = perm[e[0]], perm[e[1]]
    return (u, v) if u < v else (v, u)


orbit_of, sizes = {}, []
for e in core.EDGES:
    if e in orbit_of:
        continue
    oid, cur, k = len(sizes), e, 0
    while True:
        orbit_of[cur] = oid
        cur = pi_edge(cur)
        k += 1
        if cur == e:
            break
    sizes.append(k)
NO = len(sizes)
print(f"type {tag}: {NO} orbits, sizes {sorted(set(sizes))}", flush=True)

# quick counting feasibility: can orbit sizes be partitioned into 5 groups each >= 56?
# (necessary since Turán floor 55 is clique-partition-only => K_6 => dead; so >= 56)
import itertools as it

def var(o, c):
    return o * 5 + c + 1

clauses = []
for o in range(NO):
    clauses.append([var(o, c) for c in range(5)])
    for c, d in combinations(range(5), 2):
        clauses.append([-var(o, c), -var(o, d)])
clauses.append([var(0, 0)])  # color relabel partial break

t0 = time.time()
for S in combinations(range(26), 6):
    oset = sorted({orbit_of[(u, v)] for u, v in combinations(S, 2)})
    for c in range(5):
        clauses.append([var(o, c) for o in oset])
print(f"built {len(clauses)} clauses in {time.time()-t0:.1f}s", flush=True)

from pysat.solvers import Kissat404

t0 = time.time()
with Kissat404(bootstrap_with=clauses) as slv:
    sat = slv.solve()
    print(f"type {tag}: {'SAT' if sat else 'UNSAT'} in {time.time()-t0:.1f}s", flush=True)
    model = slv.get_model() if sat else None

if not sat:
    print(f"VERDICT fixing type {tag}: UNSAT.")
    sys.exit(0)

pos = set(l for l in model if 0 < l <= NO * 5)
coloring = [None] * 325
for e in core.EDGES:
    o = orbit_of[e]
    coloring[core.edge_id(*e)] = [c for c in range(5) if var(o, c) in pos][0]
rep = core.verify_and_report(coloring)
print(rep)
if rep["is_counterexample"]:
    with open("/Users/williamblair/personal/lean-proofs/compute617/witness.json", "w") as f:
        json.dump(coloring, f)
    print(f"!!!! COUNTEREXAMPLE FOUND (fixing type {tag}) — witness.json saved !!!!")
