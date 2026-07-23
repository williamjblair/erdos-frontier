"""E3: sigma5-equivariant colorings (pentagon generalization).

sigma = (+5 on Z_25), fixes vertex 25 (infinity).  Cycle type 5^5 * 1,
no fixed edges -> 65 edge-orbits of size 5.  Equivariant coloring:
color(sigma e) = color(e) + 1 (mod 5).  Then G_c = sigma^c(G_0), all five
classes isomorphic, so the whole problem reduces to: choose a phase
p_o in Z_5 for each orbit o; G_0 = { e : p_{o_e} + k_e = 0 (mod 5) }
(one edge per orbit, 65 edges) and require alpha(G_0) <= 5, i.e. every
6-subset of the 26 vertices contains an edge of G_0.

SAT: vars y[o][p] one-hot (325 vars), one 15-literal clause per 6-set
(230230 clauses).  SAT -> counterexample to Erdos #617 instantly.
"""
import json, sys, time
from itertools import combinations

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute617")
import core

N, INF = 26, 25


def sigma(v):
    return v if v == INF else (v + 5) % 25


def sigma_edge(e):
    u, v = sigma(e[0]), sigma(e[1])
    return (u, v) if u < v else (v, u)


# --- edge orbits ---
orbit_of = {}          # edge -> (orbit_id, shift k) with e = sigma^k(rep)
orbits = []            # orbit_id -> list of edges in shift order
for e in core.EDGES:
    if e in orbit_of:
        continue
    oid = len(orbits)
    cur, chain = e, []
    for k in range(5):
        orbit_of[cur] = (oid, k)
        chain.append(cur)
        cur = sigma_edge(cur)
    assert cur == e, "orbit size must be 5"
    orbits.append(chain)
assert len(orbits) == 65, len(orbits)

# literal for "edge e is in G_0": y[o][(-k) % 5]
def var(o, p):
    return o * 5 + p + 1  # 1..325

edge_lit = {}
for e, (o, k) in orbit_of.items():
    edge_lit[e] = var(o, (-k) % 5)

clauses = []
# one-hot phases
for o in range(65):
    clauses.append([var(o, p) for p in range(5)])
    for p, q in combinations(range(5), 2):
        clauses.append([-var(o, p), -var(o, q)])
# symmetry: cyclic color rotation -> fix phase of orbit 0
clauses.append([var(0, 0)])

# every 6-set contains a G_0 edge
t0 = time.time()
for S in combinations(range(N), 6):
    lits = set()
    for u, v in combinations(S, 2):
        lits.add(edge_lit[(u, v)])
    clauses.append(sorted(lits))
print(f"built {len(clauses)} clauses in {time.time()-t0:.1f}s", flush=True)

from pysat.solvers import Kissat404

t0 = time.time()
with Kissat404(bootstrap_with=clauses) as s:
    sat = s.solve()
    print(f"solve: {sat} in {time.time()-t0:.1f}s", flush=True)
    model = s.get_model() if sat else None

if not sat:
    print("E3 VERDICT: UNSAT — no sigma5-equivariant counterexample exists.")
    sys.exit(0)

# --- reconstruct full coloring ---
pos = set(l for l in model if l > 0)
phase = {}
for o in range(65):
    ps = [p for p in range(5) if var(o, p) in pos]
    assert len(ps) == 1
    phase[o] = ps[0]

coloring = [None] * 325
for e in core.EDGES:
    o, k = orbit_of[e]
    coloring[core.edge_id(*e)] = (phase[o] + k) % 5

rep = core.verify_and_report(coloring)
print(rep)
if rep["is_counterexample"]:
    with open("/Users/williamblair/personal/lean-proofs/compute617/witness.json", "w") as f:
        json.dump(coloring, f)
    print("!!!! COUNTEREXAMPLE FOUND (E3 equivariant) — witness.json saved !!!!")
else:
    print("E3 model failed verification — encoding bug, investigate.")
