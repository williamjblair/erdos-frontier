"""Complete enumeration of Z_5^2-translation-invariant valid K_25 colorings.

Vertices = F_5^2 (v = 5a+b).  A coloring invariant under all 25 translations
is constant on the 12 difference classes {+-d}.  SAT over 60 vars (12 orbits
x 5 colors), validity = every 6-set sees all 5 colors, enumerated exhaustively
with blocking clauses; solutions deduped under the normalizer action
GL(2,5) (480) x color perms (canonical first-occurrence relabeling).

For each iso rep: exact h_c per class (w3_certificate) + extension SAT.
The AG(2,5) coloring IS in this family (color = slope class of the
difference), so the run self-validates by finding it.
"""
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from pysat.solvers import Cadical195
from w3_extend import E25, EIDX25, check_valid_k25, extension_sat
from w3_certificate import class_graph, min_admissible_hitting_set

# ---- difference classes ----------------------------------------------------
def vid(a, b):
    return 5 * (a % 5) + (b % 5)


DIFFS = [(a, b) for a in range(5) for b in range(5) if (a, b) != (0, 0)]
orbit_of_diff = {}
ORB = []  # representative diffs
for d in DIFFS:
    if d in orbit_of_diff:
        continue
    o = len(ORB)
    nd = ((-d[0]) % 5, (-d[1]) % 5)
    orbit_of_diff[d] = o
    orbit_of_diff[nd] = o
    ORB.append(d)
assert len(ORB) == 12

def edge_orbit(u, v):
    da, db = (u // 5 - v // 5) % 5, (u % 5 - v % 5) % 5
    return orbit_of_diff[(da, db)]

EORB = [edge_orbit(u, v) for u, v in E25]

# ---- SAT enumeration --------------------------------------------------------
def var(o, c):
    return 5 * o + c + 1

cls = []
for o in range(12):
    cls.append([var(o, c) for c in range(5)])
    for c, d in combinations(range(5), 2):
        cls.append([-var(o, c), -var(o, d)])
t0 = time.time()
seen_constraints = set()
for S in combinations(range(25), 6):
    oset = tuple(sorted({EORB[EIDX25[e]] for e in combinations(S, 2)}))
    if oset in seen_constraints:
        continue
    seen_constraints.add(oset)
    for c in range(5):
        cls.append([var(o, c) for o in oset])
print(f'{len(cls)} clauses ({len(seen_constraints)} distinct orbit-6sets) '
      f'in {time.time()-t0:.1f}s', flush=True)

# ---- normalizer: GL(2,5) on difference classes ------------------------------
GL = []
for m00 in range(5):
    for m01 in range(5):
        for m10 in range(5):
            for m11 in range(5):
                if (m00 * m11 - m01 * m10) % 5 != 0:
                    GL.append((m00, m01, m10, m11))
assert len(GL) == 480
GL_PERMS = []
for (m00, m01, m10, m11) in GL:
    p = [0] * 12
    for o, (a, b) in enumerate(ORB):
        na, nb = (m00 * a + m01 * b) % 5, (m10 * a + m11 * b) % 5
        p[o] = orbit_of_diff[(na, nb)]
    GL_PERMS.append(tuple(p))
GL_PERMS = sorted(set(GL_PERMS))
print(f'{len(GL_PERMS)} distinct GL-induced orbit permutations', flush=True)


def canon(assign):
    """min over GL perms of first-occurrence color relabeling."""
    best = None
    for p in GL_PERMS:
        a2 = [0] * 12
        for o in range(12):
            a2[p[o]] = assign[o]
        # first-occurrence relabel
        relab, nxt, out = {}, 0, []
        for x in a2:
            if x not in relab:
                relab[x] = nxt
                nxt += 1
            out.append(relab[x])
        t = tuple(out)
        if best is None or t < best:
            best = t
    return best


def expand(assign):
    return [assign[EORB[k]] for k in range(300)]

# ---- enumerate ---------------------------------------------------------------
sols = []
t0 = time.time()
with Cadical195(bootstrap_with=cls) as s:
    while s.solve():
        model = set(l for l in s.get_model() if l > 0)
        assign = tuple([c for c in range(5) if var(o, c) in model][0]
                       for o in range(12))
        sols.append(assign)
        s.add_clause([-var(o, assign[o]) for o in range(12)])
        if len(sols) % 500 == 0:
            print(f'  {len(sols)} raw solutions...', flush=True)
print(f'ENUMERATION COMPLETE: {len(sols)} raw solutions in '
      f'{time.time()-t0:.1f}s', flush=True)

reps = {}
for a in sols:
    reps.setdefault(canon(a), a)
print(f'{len(reps)} classes up to GL(2,5) x color perms', flush=True)

for i, (cn, a) in enumerate(sorted(reps.items())):
    col = expand(a)
    bad = check_valid_k25(col)
    assert bad == 0, f'enumerated solution INVALID: {bad} bad 6-sets'
    sizes = sorted(sum(1 for k in range(300) if col[k] == c) for c in range(5))
    hs = []
    for c in range(5):
        h, ni, ncl, _ = min_admissible_hitting_set(class_graph(col, c))
        hs.append(h)
    att = extension_sat(col, verbose=False)
    print(f'rep#{i}: orbit-colors={a} sizes={sizes} h={hs} sum_h={sum(hs)} '
          f'ext={"SAT!!!" if att is not None else "UNSAT"}', flush=True)
    if att is not None:
        print('!!!! EXTENDABLE TRANSLATION-INVARIANT K_25 — investigate '
              'immediately !!!!', flush=True)
print('DONE', flush=True)
