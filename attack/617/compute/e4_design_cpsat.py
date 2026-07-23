"""E4: five pairwise edge-disjoint {6,5,5,5,5}-clique-partitions of 26 points
(social-golfer-like resolvable packing; 275 of 325 pairs used).

If found: color each partition's clique edges with its class colour, then dump
the 50 leftover edges anywhere (say colour 0) — every class contains a
spanning {6,5,5,5,5} clique partition, hence alpha <= 5.  Instant win.

CP-SAT model: y[c][v][k] = vertex v in block k of class c (block 0 has 6
vertices, blocks 1..4 have 5).  Pair used at most once overall.
"""
import json, sys, time
from itertools import combinations

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute617")
import core
from ortools.sat.python import cp_model

N, C, K = 26, 5, 5
SIZES = [6, 5, 5, 5, 5]

m = cp_model.CpModel()
y = {}
for c in range(C):
    for v in range(N):
        for k in range(K):
            y[c, v, k] = m.NewBoolVar(f"y_{c}_{v}_{k}")
        m.AddExactlyOne(y[c, v, k] for k in range(K))
    for k in range(K):
        m.Add(sum(y[c, v, k] for v in range(N)) == SIZES[k])

# class 0 fixed: consecutive blocks (symmetry breaking)
fixed0 = [list(range(0, 6)), list(range(6, 11)), list(range(11, 16)),
          list(range(16, 21)), list(range(21, 26))]
for k, blk in enumerate(fixed0):
    for v in blk:
        m.Add(y[0, v, k] == 1)

# WLOG within classes >=1: vertex 0 in block 0 or 1 (5-blocks relabelable)
for c in range(1, C):
    m.AddBoolOr([y[c, 0, 0], y[c, 0, 1]])

# pair together at most once across all classes/blocks
pairs = list(combinations(range(N), 2))
together = {}
for c in range(C):
    for (u, v) in pairs:
        for k in range(K):
            t = m.NewBoolVar(f"t_{c}_{u}_{v}_{k}")
            m.AddImplication(t, y[c, u, k])
            m.AddImplication(t, y[c, v, k])
            m.AddBoolOr([y[c, u, k].Not(), y[c, v, k].Not(), t])
            together[c, u, v, k] = t
for (u, v) in pairs:
    m.Add(sum(together[c, u, v, k] for c in range(C) for k in range(K)) <= 1)

solver = cp_model.CpSolver()
solver.parameters.num_search_workers = 12
solver.parameters.max_time_in_seconds = 7200
solver.parameters.log_search_progress = False
t0 = time.time()
status = solver.Solve(m)
print(f"status: {solver.StatusName(status)} in {time.time()-t0:.1f}s", flush=True)

if status not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
    print("E4 VERDICT: no design found (INFEASIBLE or timeout).")
    sys.exit(0)

partitions = []
for c in range(C):
    blocks = []
    for k in range(K):
        blocks.append([v for v in range(N) if solver.Value(y[c, v, k])])
    partitions.append(blocks)
print(json.dumps(partitions))

# build coloring: clique edges of class c get colour c; leftovers colour 0
coloring = [None] * 325
for c, blocks in enumerate(partitions):
    for blk in blocks:
        for u, v in combinations(blk, 2):
            eid = core.edge_id(u, v)
            assert coloring[eid] is None, "pair reused!"
            coloring[eid] = c
free = [i for i, x in enumerate(coloring) if x is None]
print(f"free edges: {len(free)}")
for i in free:
    coloring[i] = 0

rep = core.verify_and_report(coloring)
print(rep)
if rep["is_counterexample"]:
    with open("/Users/williamblair/personal/lean-proofs/compute617/witness.json", "w") as f:
        json.dump(coloring, f)
    with open("/Users/williamblair/personal/lean-proofs/compute617/design_e4.json", "w") as f:
        json.dump(partitions, f)
    print("!!!! COUNTEREXAMPLE FOUND (E4 design) — witness.json saved !!!!")
else:
    print("E4 design found but verification failed — bug, investigate.")
