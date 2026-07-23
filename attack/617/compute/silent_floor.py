"""Silent-class edge floor in isolation: min edges of a graph on 25
vertices with alpha <= 4 (every 5-set spans an edge) and omega <= 5
(K_6-free — mandatory for any class of a valid coloring).

Hand bound (banked): >= 67 (66 forces complement = Turan K_{7,6,6,6} by
extremal uniqueness => G = K_7+3K_6 contains K_6).  This probe sharpens it:
UNSAT at <= 75 => silent floor >= 76 => cube s=2 needs 2*76+3*50 = 302 >
300 edges => s <= 1.  SAT gives the true floor via descent.

Usage: python3 silent_floor.py <start_bound>
"""
import sys
import time
from itertools import combinations

from pysat.card import CardEnc, EncType
from pysat.solvers import Kissat404

E25 = list(combinations(range(25), 2))
EIDX = {e: k for k, e in enumerate(E25)}

base = []
for T in combinations(range(25), 5):
    base.append([EIDX[e] + 1 for e in combinations(T, 2)])   # alpha<=4
for S in combinations(range(25), 6):
    base.append([-(EIDX[e] + 1) for e in combinations(S, 2)])  # K_6-free
print(f'base: {len(base)} clauses', flush=True)


def feasible(bound):
    cnf = list(base)
    enc = CardEnc.atmost(lits=list(range(1, 301)), bound=bound,
                         top_id=400, encoding=EncType.seqcounter)
    cnf.extend(enc.clauses)
    t0 = time.time()
    with Kissat404(bootstrap_with=cnf) as s:
        sat = s.solve()
        print(f'  <= {bound} edges: {"SAT" if sat else "UNSAT"} '
              f'({time.time()-t0:.1f}s)', flush=True)
        if sat:
            model = set(l for l in s.get_model() if l > 0)
            g = [k for k in range(300) if k + 1 in model]
            return g
    return None


start = int(sys.argv[1])
g = feasible(start)
if g is None:
    print(f'VERDICT: silent floor >= {start+1}', flush=True)
    if start >= 75:
        print('*** => cube s=2 EMPTY by edge counting (2 silents + 3 louds '
              '> 300 edges) — only s in {0,1} remain ***', flush=True)
else:
    print(f'{start} achievable; witness has {len(g)} edges — descending',
          flush=True)
    lo, hi = 67, len(g)
    while lo < hi:
        mid = (lo + hi) // 2
        r = feasible(mid)
        if r is None:
            lo = mid + 1
        else:
            hi = min(mid, len(r))
    print(f'SILENT FLOOR = {lo}', flush=True)
