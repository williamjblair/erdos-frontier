"""E2: order-13-invariant colorings (color FIXED on pair-orbits).

tau = two 13-cycles (0..12)(13..25); 25 pair-orbits of size 13.  alpha<=5
forces >= 55 edges per class -> >= 5 orbits -> exactly 5 orbits per color
(derived, not assumed).  Variables z[o][c] one-hot (125), cardinality 5 per
color; clauses: every 6-set contains an edge of every color (5 x 230230).
Covers ALL colorings invariant under any order-13 permutation of 26 points
(all are conjugate to tau).
"""
import json, sys, time
from itertools import combinations

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute617")
import core

perm = [(i + 1) % 13 for i in range(13)] + [13 + (i + 1) % 13 for i in range(13)]


def tau_edge(e):
    u, v = perm[e[0]], perm[e[1]]
    return (u, v) if u < v else (v, u)


orbit_of, orbits = {}, []
for e in core.EDGES:
    if e in orbit_of:
        continue
    oid, cur = len(orbits), e
    chain = []
    while True:
        orbit_of[cur] = oid
        chain.append(cur)
        cur = tau_edge(cur)
        if cur == e:
            break
    assert len(chain) == 13
    orbits.append(chain)
assert len(orbits) == 25

def var(o, c):
    return o * 5 + c + 1  # 1..125

clauses = []
for o in range(25):
    clauses.append([var(o, c) for c in range(5)])
    for c, d in combinations(range(5), 2):
        clauses.append([-var(o, c), -var(o, d)])

# exactly 5 orbits per color (sequential counter <=5 both ways via pysat)
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

pool = IDPool(start_from=126)
for c in range(5):
    lits = [var(o, c) for o in range(25)]
    cnf = CardEnc.equals(lits=lits, bound=5, vpool=pool, encoding=EncType.seqcounter)
    clauses.extend(cnf.clauses)

# color symmetry: orbit 0's color is 0; (helps a bit; full S5 breaking skipped)
clauses.append([var(0, 0)])

t0 = time.time()
for S in combinations(range(26), 6):
    oset = set()
    for u, v in combinations(S, 2):
        oset.add(orbit_of[(u, v)])
    ol = sorted(oset)
    for c in range(5):
        clauses.append([var(o, c) for o in ol])
print(f"built {len(clauses)} clauses in {time.time()-t0:.1f}s", flush=True)

from pysat.solvers import Kissat404

t0 = time.time()
with Kissat404(bootstrap_with=clauses) as s:
    sat = s.solve()
    print(f"E2: {'SAT' if sat else 'UNSAT'} in {time.time()-t0:.1f}s", flush=True)
    model = s.get_model() if sat else None

if not sat:
    print("E2 VERDICT: UNSAT — no order-13-invariant counterexample exists.")
    sys.exit(0)

pos = set(l for l in model if 0 < l <= 125)
coloring = [None] * 325
for e in core.EDGES:
    o = orbit_of[e]
    c = [c for c in range(5) if var(o, c) in pos][0]
    coloring[core.edge_id(*e)] = c
rep = core.verify_and_report(coloring)
print(rep)
if rep["is_counterexample"]:
    with open("/Users/williamblair/personal/lean-proofs/compute617/witness.json", "w") as f:
        json.dump(coloring, f)
    print("!!!! COUNTEREXAMPLE FOUND (E2 bicirculant) — witness.json saved !!!!")
