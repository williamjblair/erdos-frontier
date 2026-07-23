#!/usr/bin/env python3
"""Independent spot checks of the regenerated deterministic tables (gate-1 addendum).

  [S1] Moment count tensors P^sigma(H): re-count with MY OWN implementation (own
       root-fixed canonical form, own sigma-induction test, own disjoint-pair loop)
       for ALL 1897 states on the K0 block, and for a seeded random sample of 200
       (label, state) pairs on K1/EDGE/NON. Compare full t x t integer matrices
       against the regenerated Pint.
  [S2] Lift matrix D: for a seeded random sample of 500 of the 12,172 order-10
       states, decode graph6 MYSELF, delete each vertex, canonicalize the 9-vertex
       remainder with nauty `labelg` (independent third-party canonizer), and match
       into the labelg-canonicalized T_9 list. Compare the resulting column
       (multiplicities/10) with the regenerated c5lift D column, exactly.

Seeded and reproducible (seed 20260710).
"""
import itertools, os, pickle, random, subprocess, sys, time
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
os.chdir(HERE)
SEED = 20260710
GENG = "/opt/homebrew/bin/geng"
LABELG = "/opt/homebrew/bin/labelg"
STAGE = sys.argv[1] if len(sys.argv) > 1 else "all"   # s1 | s2 | all
t0 = time.time()
def log(m): print(f"[{time.time()-t0:6.0f}s] {m}", flush=True)

states9, dedge9, moments = pickle.load(open("my_moments_n9.pkl", "rb"))

# ---------------- my own primitives (written fresh, no author code) ----------------
def my_edge(A, i, j): return (A[i] >> j) & 1

def my_root_canonical(m, A, k):
    """lex-min upper-triangle bit tuple over permutations fixing vertices 0..k-1."""
    best = None
    for p in itertools.permutations(range(k, m)):
        perm = list(range(k)) + list(p)
        bits = tuple(1 if my_edge(A, perm[i], perm[j]) else 0
                     for i in range(m) for j in range(i + 1, m))
        if best is None or bits < best:
            best = bits
    return best

def my_induces_sigma(A, R, k, Asig):
    for a in range(k):
        for b in range(a + 1, k):
            if my_edge(A, R[a], R[b]) != ((Asig[a] >> b) & 1):
                return False
    return True

def my_sub_adj(A, verts):
    m = len(verts)
    B = [0] * m
    for a in range(m):
        for b in range(a + 1, m):
            if my_edge(A, verts[a], verts[b]):
                B[a] |= 1 << b; B[b] |= 1 << a
    return B

def my_P_matrix(n, A, k, Asig, s, flagkeys):
    tt = len(flagkeys)
    M = [[0] * tt for _ in range(tt)]
    for R in itertools.permutations(range(n), k):
        if not my_induces_sigma(A, R, k, Asig):
            continue
        rest = [v for v in range(n) if v not in R]
        subs = list(itertools.combinations(rest, s))
        idxs = []
        for S in subs:
            B = my_sub_adj(A, list(R) + list(S))
            idxs.append(flagkeys.get(my_root_canonical(k + s, B, k), -1))
        for a in range(len(subs)):
            ia = idxs[a]
            if ia < 0: continue
            Sa = set(subs[a])
            for b in range(len(subs)):
                ib = idxs[b]
                if ib < 0: continue
                if Sa & set(subs[b]): continue
                M[ia][ib] += 1
    return M

# flag key maps (author's flag list as basis definition; MY canonical for keys)
flagmaps = {}
for (lab, tt, sigma, flags, s, Pint) in moments:
    k, Asig = sigma
    fk = {}
    for idx, (fm, fA) in enumerate(flags):
        key = my_root_canonical(fm, fA, k)
        assert key not in fk, "my canonical collides on flags"
        fk[key] = idx
    flagmaps[lab] = fk

ok_s1a = ok_s1b = None
if STAGE in ("s1", "all"):
    # [S1a] K0 block, ALL states
    lab, tt, sigma, flags, s, Pint = next(m for m in moments if m[0] == "K0")
    k, Asig = sigma
    bad = 0
    for hi, (n, A) in enumerate(states9):
        M = my_P_matrix(n, A, k, Asig, s, flagmaps["K0"])
        if any(int(Pint[hi][a][b]) != M[a][b] for a in range(tt) for b in range(tt)):
            bad += 1
    log(f"[S1a] K0 full recount, all 1897 states: mismatching matrices = {bad}")
    ok_s1a = (bad == 0)

    # [S1b] seeded sample of 200 (label, state) pairs over K1/EDGE/NON
    rng = random.Random(SEED)
    pairs = [(lab, rng.randrange(1897)) for lab in ("K1", "EDGE", "NON") for _ in range(67)][:200]
    bad = 0
    for (lab, hi) in pairs:
        _, tt, sigma, flags, s, Pint = next(m for m in moments if m[0] == lab)
        k, Asig = sigma
        n, A = states9[hi]
        M = my_P_matrix(n, A, k, Asig, s, flagmaps[lab])
        if any(int(Pint[hi][a][b]) != M[a][b] for a in range(tt) for b in range(tt)):
            bad += 1
    log(f"[S1b] sampled recount K1/EDGE/NON, {len(pairs)} (label,state) pairs: mismatches = {bad}")
    ok_s1b = (bad == 0)

# ---------------- [S2] D columns via labelg ----------------
def decode_g6(line):
    b = [ord(ch) - 63 for ch in line.strip()]
    n = b[0]; bits = []
    for x in b[1:]:
        bits += [(x >> k2) & 1 for k2 in range(5, -1, -1)]
    A = [0] * n; idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                A[i] |= 1 << j; A[j] |= 1 << i
            idx += 1
    return n, A

def encode_g6(n, A):
    bits = []
    for j in range(1, n):
        for i in range(j):
            bits.append(1 if my_edge(A, i, j) else 0)
    while len(bits) % 6:
        bits.append(0)
    out = chr(n + 63)
    for i in range(0, len(bits), 6):
        v = 0
        for b in bits[i:i+6]:
            v = (v << 1) | b
        out += chr(v + 63)
    return out

def labelg_batch(lines):
    r = subprocess.run([LABELG, "-q"], input="\n".join(lines) + "\n",
                       capture_output=True, text=True)
    return r.stdout.splitlines()

ok_s2 = None
if STAGE not in ("s2", "all"):
    print()
    allok = bool(ok_s1a) and bool(ok_s1b)
    print(f">>> SPOTCHECK[{STAGE}]: {'ALL PASS' if allok else 'FAILURES PRESENT'} "
          f"(S1a K0-all={ok_s1a}, S1b sample200={ok_s1b}) <<<", flush=True)
    sys.exit(0 if allok else 1)

# canonical T_9 map (labelg over geng output; independent of author's ordering logic)
g6_9 = subprocess.run([GENG, "-q", "-t", "9"], capture_output=True, text=True).stdout.splitlines()
assert len(g6_9) == 1897
canon9 = labelg_batch(g6_9)
canonmap9 = {c: i for i, c in enumerate(canon9)}
assert len(canonmap9) == 1897
# check my states9 (author-pipeline enumeration) matches geng order 1:1 through labelg
mine_canon = labelg_batch([encode_g6(n, A) for (n, A) in states9])
perm_ok = all(canonmap9[mine_canon[i]] == i for i in range(1897))
log(f"[S2] states9 (author pipeline) aligns index-for-index with my geng/labelg T_9: {perm_ok}")

d = np.load("c5lift_cache.npz", allow_pickle=True)
from scipy.sparse import csr_matrix
D = csr_matrix((d["Dval"], (d["Drow"], d["Dcol"])), shape=(1897, int(d["nJ"]))).tocsc()
g6_10 = subprocess.run([GENG, "-q", "-t", "10"], capture_output=True, text=True).stdout.splitlines()
cols = random.Random(SEED + 1).sample(range(12172), 500)
bad = 0
for c in cols:
    n, A = decode_g6(g6_10[c])
    sub_lines = []
    for v in range(10):
        verts = [u for u in range(10) if u != v]
        sub_lines.append(encode_g6(9, my_sub_adj(A, verts)))
    canon_subs = labelg_batch(sub_lines)
    cnt = {}
    for cs in canon_subs:
        cnt[canonmap9[cs]] = cnt.get(canonmap9[cs], 0) + 1
    col = D.getcol(c).tocoo()
    mine = {r: Fr(v2, 10) for r, v2 in cnt.items()}
    theirs = {int(r): Fr(float(v2)).limit_denominator(10**6) for r, v2 in zip(col.row, col.data)}
    if mine != theirs:
        bad += 1
log(f"[S2] D columns, 500 seeded samples: mismatching columns = {bad}")
ok_s2 = (bad == 0) and perm_ok

print()
checks = [c for c in (ok_s1a, ok_s1b, ok_s2) if c is not None]
allok = all(checks) and checks
print(f">>> SPOTCHECK[{STAGE}]: {'ALL PASS' if allok else 'FAILURES PRESENT'} "
      f"(S1a K0-all={ok_s1a}, S1b sample200={ok_s1b}, S2 D500={ok_s2}) <<<", flush=True)
sys.exit(0 if allok else 1)
