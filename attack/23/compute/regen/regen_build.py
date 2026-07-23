#!/usr/bin/env python3
"""Gate-1 addendum: deterministic regeneration of the combinatorial tables needed by
condition 4's MOMENT side, plus exact recomputation of the moment term and bit-for-bit
comparison against the frozen mom_term_exact.pkl.

Stages (all pure counting / exact rational arithmetic; NO LP is solved anywhere):
  1. states9 (geng -t 9) + dedge + the four moment blocks (K0,K1,EDGE,NON) via the
     author's fc.moment_types / fs.P_sigma (integer count tensors). Trimmed build_cache:
     Gbase/deftypes/localizer blobs are skipped (unused by the verification path).
  2. c5lift_cache.npz via the author's c5_lift_diag.build (vertex-deletion marginal D,
     gamma, pC5) -- deterministic combinatorics.
  3. Exact moment term over the 12,172 order-10 states, replicating the arithmetic of
     complete_v2_cert.py lines 52-74 (same rationalization conventions), from the
     REGENERATED tables + the SHIPPED Gram atoms; bit-for-bit compare vs the shipped
     mom_term_exact.pkl. Also: exact D sanity (column sums = 1; 45*(D^T dedge9) equals
     integer edge counts from an independent decode).
"""
import io, itertools, os, pickle, subprocess, sys, time
from fractions import Fraction as Fr
from math import comb, prod
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.join(HERE, "..", "src", "anc")
os.chdir(HERE)
sys.path.insert(0, HERE)

import flag_engine as fe
fe.GENG = "/opt/homebrew/bin/geng"          # only patch: geng path (author's is Windows)
import flag_sdp as fs
import flag_cutgen as fc
import flag_exact as fx
import c5_lift_diag as cl

t0 = time.time()
def log(msg): print(f"[{time.time()-t0:7.0f}s] {msg}", flush=True)

class RU(pickle.Unpickler):
    def find_class(self, m, n): raise pickle.UnpicklingError("forbidden")
def load_anc(fn):
    with open(os.path.join(ANC, fn), "rb") as f:
        return RU(io.BytesIO(f.read())).load()

# ---------------- stage 1: states + moment tables ----------------
if os.path.exists("my_moments_n9.pkl"):
    states9, dedge9, moments = pickle.load(open("my_moments_n9.pkl", "rb"))
    log(f"stage1: loaded cached my_moments_n9.pkl ({len(states9)} states)")
else:
    states9 = fe.enumerate_graphs(9, triangle_free=True)
    assert len(states9) == 1897, len(states9)
    dedge9 = fs.edge_density(states9)
    log(f"stage1: {len(states9)} order-9 states enumerated")
    moments = []
    for (lab, sigma, flags) in fc.moment_types(9, smax=None):
        mats = fs.P_sigma(9, states9, sigma, flags)
        tt = len(flags); k = sigma[0]; s = flags[0][0] - k
        Pint = [np.rint(m).astype(np.int64) for m in mats]
        moments.append((lab, tt, sigma, flags, s, Pint))
        log(f"stage1: moment block {lab}: t={tt} s={s} built")
    pickle.dump((states9, dedge9, moments), open("my_moments_n9.pkl", "wb"), protocol=4)
    log("stage1: saved my_moments_n9.pkl")
exp_dims = {"K0": 7, "K1": 35, "EDGE": 34, "NON": 57}   # per shipped moment_gram_w.pkl atoms
for (lab, tt, sigma, flags, s, Pint) in moments:
    assert tt == exp_dims[lab], (lab, tt)
log(f"stage1 OK: flag dims match shipped atom dims {exp_dims}")

# ---------------- stage 2: c5 lift ----------------
Drow, Dcol, Dval, gam, pC5, nJ = cl.build(states9)     # writes/reads c5lift_cache.npz
assert nJ == 12172, nJ
log(f"stage2 OK: D built, nnz={len(Dval)}, nJ={nJ}")

# exact D sanity: column sums == 1 and 45*(D^T dedge9)[s] == e(G_s) from independent decode
colsum = {}
Dtrip = []
for r, c, v in zip(Drow, Dcol, Dval):
    fv = Fr(float(v)).limit_denominator(10**6)          # same convention as complete_v2_cert.py
    Dtrip.append((int(r), int(c), fv))
    colsum[int(c)] = colsum.get(int(c), Fr(0)) + fv
assert all(colsum[c] == 1 for c in range(nJ)), "D column sums != 1"
dedge9_f = [Fr(int(round(float(d) * 36)), 36) for d in dedge9]   # order-9: C(9,2)=36
assert all(Fr(float(dedge9[i])).limit_denominator(10**6) == dedge9_f[i] for i in range(1897))
dedge_q = [Fr(0)] * nJ
for (r, c, v) in Dtrip:
    dedge_q[c] += v * dedge9_f[r]
# independent T_10 decode (own graph6 reader, geng direct)
def decode_g6(line):
    b = [ord(ch) - 63 for ch in line.strip()]
    n = b[0]; bits = []
    for x in b[1:]:
        bits += [(x >> k) & 1 for k in range(5, -1, -1)]
    A = [0] * n; idx = 0
    for j in range(1, n):
        for i in range(j):
            if bits[idx]:
                A[i] |= 1 << j; A[j] |= 1 << i
            idx += 1
    return n, A
g6_10 = subprocess.run(["/opt/homebrew/bin/geng", "-q", "-t", "10"],
                       capture_output=True, text=True).stdout.splitlines()
assert len(g6_10) == nJ
e10 = []
for line in g6_10:
    n, A = decode_g6(line)
    e10.append(sum(bin(a).count("1") for a in A) // 2)
ok_dedge = all(dedge_q[s] == Fr(e10[s], 45) for s in range(nJ))
log(f"stage2 sanity: 45*(D^T dedge9) == independent edge counts for all {nJ} states: {ok_dedge}")
assert ok_dedge

# ---------------- stage 3: exact moment term, bit-for-bit vs shipped ----------------
W = load_anc("moment_gram_w.pkl")
sup = W["support"]; labs = W["atoms_lab"]; vvs = W["atoms_vv"]
supw = [W["w"][i] for i in sup]
labinfo = {}
for (lab, tt, sigma, flags, s, Pint) in moments:
    k = sigma[0]
    den = [Fr(int((prod(n - i for i in range(k)) * comb(n - k, s) ** 2) if (n - k >= s) else 1) or 1)
           for (n, A) in states9]
    labinfo[lab] = (Pint, den)
MD_V = 10**6
mom = [Fr(0)] * nJ
for ci, (lab, vv, wf) in enumerate(zip(labs, vvs, supw)):
    if wf <= 1e-13:
        continue
    w_c = Fr(float(wf)).limit_denominator(MD_V)
    Pint, den = labinfo[lab]
    vr = fx.rat_vec(np.asarray(vv), MD_V)
    bc = fx.moment_cut_exact(Pint, vr, den)
    for (r, c, coef) in Dtrip:
        if bc[r] != 0:
            mom[c] += w_c * coef * bc[r]
    if (ci + 1) % 10 == 0:
        log(f"stage3: atom {ci+1}/{len(sup)}")
shipped = [Fr(n, d) for (n, d) in load_anc("mom_term_exact.pkl")]
assert len(shipped) == nJ
neq = sum(1 for s in range(nJ) if mom[s] != shipped[s])
log(f"stage3: bit-for-bit compare vs shipped mom_term_exact.pkl: mismatches = {neq} / {nJ}")
if neq:
    bad = [s for s in range(nJ) if mom[s] != shipped[s]][:10]
    log(f"stage3: first mismatched states: {bad}")
    for s in bad[:3]:
        log(f"  state {s}: mine={mom[s]}  shipped={shipped[s]}")
pickle.dump([(m.numerator, m.denominator) for m in mom], open("my_mom_term_exact.pkl", "wb"))
print(f"\n>>> REGEN RESULT: moment term {'MATCHES SHIPPED BIT-FOR-BIT (12172/12172)' if neq==0 else f'MISMATCH on {neq} states'} <<<", flush=True)
