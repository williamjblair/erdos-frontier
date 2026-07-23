"""Generic color-cycling SAT: permutation pi on 26 vertices, coloring with
color(pi e) = color(e) + 1 (mod 5).  Requires every edge-orbit size divisible
by 5; then G_c = pi^c(G_0) (all classes isomorphic) and the problem reduces to
alpha(G_0) <= 5 where G_0 picks edges e with phase[orbit] + shift(e) = 0 mod 5.

Cycle types (partitions of 25 into parts from {5,10,15,20,25}, plus one fixed
point) are the only possibilities.  Usage: python3 cycling_sat.py 25 / 20,5 /
15,10 / 15,5,5 / 10,10,5 / 10,5,5,5 / 5,5,5,5,5
"""
import json, sys, time
from itertools import combinations

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute617")
import core

parts = [int(x) for x in sys.argv[1].split(",")]
assert sum(parts) == 25 and all(p % 5 == 0 for p in parts)
tag = "-".join(map(str, parts))

# build pi: consecutive cycles, vertex 25 fixed
perm = list(range(26))
start = 0
for p in parts:
    for i in range(p):
        perm[start + i] = start + (i + 1) % p
    start += p
assert perm[25] == 25


def pi_edge(e):
    u, v = perm[e[0]], perm[e[1]]
    return (u, v) if u < v else (v, u)


orbit_of, orbits = {}, []
for e in core.EDGES:
    if e in orbit_of:
        continue
    oid, cur, k = len(orbits), e, 0
    chain = []
    while True:
        orbit_of[cur] = (oid, k)
        chain.append(cur)
        cur = pi_edge(cur)
        k += 1
        if cur == e:
            break
    assert len(chain) % 5 == 0, (parts, len(chain))
    orbits.append(chain)

NO = len(orbits)
print(f"type {tag}: {NO} edge orbits, sizes ok", flush=True)


def var(o, p):
    return o * 5 + p + 1


edge_lit = {e: var(o, (-k) % 5) for e, (o, k) in orbit_of.items()}

clauses = []
for o in range(NO):
    clauses.append([var(o, p) for p in range(5)])
    for p, q in combinations(range(5), 2):
        clauses.append([-var(o, p), -var(o, q)])
clauses.append([var(0, 0)])  # cyclic color-shift symmetry

for S in combinations(range(26), 6):
    lits = set()
    for u, v in combinations(S, 2):
        lits.add(edge_lit[(u, v)])
    clauses.append(sorted(lits))

from pysat.solvers import Kissat404

t0 = time.time()
with Kissat404(bootstrap_with=clauses) as s:
    sat = s.solve()
    print(f"type {tag}: {'SAT' if sat else 'UNSAT'} in {time.time()-t0:.1f}s", flush=True)
    model = s.get_model() if sat else None

if not sat:
    print(f"VERDICT type {tag}: UNSAT — no cycling counterexample of this type.")
    sys.exit(0)

pos = set(l for l in model if l > 0)
coloring = [None] * 325
for e in core.EDGES:
    o, k = orbit_of[e]
    ph = [p for p in range(5) if var(o, p) in pos][0]
    coloring[core.edge_id(*e)] = (ph + k) % 5
rep = core.verify_and_report(coloring)
print(rep)
if rep["is_counterexample"]:
    with open("/Users/williamblair/personal/lean-proofs/compute617/witness.json", "w") as f:
        json.dump(coloring, f)
    print(f"!!!! COUNTEREXAMPLE FOUND (cycling type {tag}) — witness.json saved !!!!")
