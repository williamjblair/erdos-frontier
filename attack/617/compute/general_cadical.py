"""Portfolio second opinion on the general instance with Cadical300."""
import sys, time
from itertools import combinations

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute617")
import core

def var(k, c):
    return k * 5 + c + 1

clauses = []
for k in range(325):
    clauses.append([var(k, c) for c in range(5)])
    for c, d in combinations(range(5), 2):
        clauses.append([-var(k, c), -var(k, d)])
clauses.append([var(0, 0)])
for S in combinations(range(26), 6):
    ks = [core.edge_id(u, v) for u, v in combinations(S, 2)]
    for c in range(5):
        clauses.append([var(k, c) for k in ks])
print(f"{len(clauses)} clauses", flush=True)

from pysat.solvers import Cadical300
t0 = time.time()
with Cadical300(bootstrap_with=clauses) as s:
    sat = s.solve()
    print(f"GENERAL (cadical300): {'SAT' if sat else 'UNSAT'} ({time.time()-t0:.1f}s)", flush=True)
    if sat:
        model = s.get_model()
        pos = set(l for l in model if l > 0)
        col = [[c for c in range(5) if var(k, c) in pos][0] for k in range(325)]
        rep = core.verify_and_report(col)
        print(rep)
        if rep["is_counterexample"]:
            import json
            with open("/Users/williamblair/personal/lean-proofs/compute617/witness.json", "w") as f:
                json.dump(col, f)
            print("!!!! COUNTEREXAMPLE FOUND (general, cadical) — witness.json saved !!!!")
