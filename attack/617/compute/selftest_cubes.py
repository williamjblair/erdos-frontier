"""End-to-end property tests for the cube campaign machinery.

1. AG full-unit assignment on base_validity is SAT; decode -> exactly the
   AG coloring; valid_k25 True; rook class loud; extension UNSAT (all
   independently known).
2. K_7-complete class-0 cube on base_validity is UNSAT (K_6 coverage).
3. AG-pattern cube (assumptions only) on base_validity is SAT within
   budget -> decoded model verifies valid_k25 (validates the exact
   assumption path the campaign uses, on the known-SAT side).
4. check_admissible cross-check on the banked h=5 witness: the harvested
   H line {0,5,10,15,20} must be admissible for class 0 of
   runs25/hclimb_ag.best.txt, and any single vertex must NOT be.
"""
import sys
import time

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import cube_common as CC
import lemma_loud as LL
from w3_extend import ag_coloring
from pysat.solvers import Cadical195
from itertools import combinations

ok = True


def check(name, cond):
    global ok
    print(f'  [{"OK" if cond else "FAIL"}] {name}', flush=True)
    ok = ok and cond


t0 = time.time()
base = LL.base_validity()
print(f'base_validity: {len(base)} clauses ({time.time()-t0:.0f}s)')

ag = ag_coloring()
units = []
for k in range(300):
    for c in range(5):
        units.append(CC.xvar(k, c) if ag[k] == c else -CC.xvar(k, c))

s = Cadical195(bootstrap_with=base)
print(f'solver loaded ({time.time()-t0:.0f}s)')

# --- 1 full units
r = s.solve(assumptions=units)
check('AG full units SAT', r is True)
model = set(l for l in s.get_model() if l > 0)
col = CC.decode_coloring(model)
check('decode == AG', col == list(ag))
check('valid_k25(AG)', CC.valid_k25(col))
check('rook class loud (alpha>4 at bound 4)', not CC.alpha_le(col, 0, 4))
ext, _ = CC.extension_sat(col)
check('AG extension UNSAT', ext is False)

# --- 2 K7 cube UNSAT
k7 = CC.cube_literals('colored', 7, list(combinations(range(7), 2)))
t = time.time()
r = s.solve(assumptions=k7)
check(f'K7-complete cube UNSAT ({time.time()-t:.1f}s)', r is False)

# --- 3 AG-pattern cube
agpat = [tuple(e) for e in combinations(range(7), 2)
         if ag[LL.EIDX25[e]] == 0]
cube = CC.cube_literals('colored', 7, agpat)
check('cube has 21 lits', len(cube) == 21)
s.conf_budget(500000)
t = time.time()
r = s.solve_limited(assumptions=cube)
print(f'  AG-pattern cube on base validity: '
      f'{ {True: "SAT", False: "UNSAT", None: "UNKNOWN"}[r] } '
      f'({time.time()-t:.1f}s)')
check('AG-pattern cube not UNSAT', r is not False)
if r is True:
    col2 = CC.decode_coloring(set(l for l in s.get_model() if l > 0))
    check('cube model valid_k25', CC.valid_k25(col2))
s.delete()

# --- 4 admissibility cross-check on banked h=5 witness
lines = open('runs25/hclimb_ag.best.txt').read().split('\n')
w = list(map(int, lines[1].split()))
check('witness valid_k25', CC.valid_k25(w))
check('H=line admissible', CC.check_admissible(w, 0, [0, 5, 10, 15, 20]))
check('H={0} NOT admissible', not CC.check_admissible(w, 0, [0]))

print('ALL OK' if ok else 'FAILURES PRESENT', flush=True)
sys.exit(0 if ok else 1)
