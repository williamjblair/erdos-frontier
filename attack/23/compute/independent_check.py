#!/usr/bin/env python3
"""Gate-1 INDEPENDENT minimal checker for arXiv:2606.28041 (Erdos #23, a(5n)=n^2, n<=40).

Written from scratch (not derived from the author's step1_v2_independent_gate.py).
Checks everything that is checkable from the shipped ancillary data alone, in exact
integer/Fraction arithmetic, with NO floating-point threshold comparisons:

  [A] Raw-dual re-derivation of delta_final from horn_dual.pkl
      (same declared rationalization convention: Fraction(float).limit_denominator(1e8)),
      compared bit-for-bit against the saved v2_cert_complete.pkl value.
  [B] Manifest-PSD gate: every Gram weight w_c >= 0 (all 394 atoms and the support list).
  [C] a7 + a8 == 1 exactly (from the saved producer values; NOT re-derivable from the
      package -- the env structure lives in horn_cert_state_it16.pkl, not shipped).
  [D] Closure arithmetic, exact: delta < 1/20000 <=> (25/2)*40^2*delta < 1  (n=40 closes);
      (25/2)*41^2*delta >= 1  (n=41 does not close); margin computation.
  [E] Blow-up integrality layer, verified end-to-end by brute force on small graphs:
      mc(G[t]) = t^2 mc(G) and beta(G[t]) = t^2 beta(G) for all 38 triangle-free graphs
      of order 6 with t=2, plus C5[t] for t=1..3 (beta = t^2) and C7[2].
  [F] The transfer inequality arithmetic: for N=5n, N^2/25 = n^2 and N^2*delta/2 = 25n^2 delta/2.

What this checker CANNOT verify from the package (reported, not silently assumed):
  - the per-state dual feasibility R_cbh(s) >= <Q,P(s)> over the 12172 order-10 states
    (needs cp_cache.pkl / c5lift_cache.npz / horn_cert_state_it16.pkl / prove_cert.py /
    flag_exact.py, none of which ship);
  - the derivation of a7/a8 from the raw dual (same missing env table);
  - the envelope-row coefficients g_{sigma,c} and the moment-term values.
"""
import io, pickle, sys, itertools
from fractions import Fraction as Fr

ANC = "/Users/williamblair/personal/lean-proofs/compute23/src/anc/"

# ---------- restricted unpickler: data-only pickles ----------
class RestrictedUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        raise pickle.UnpicklingError(f"global {module}.{name} forbidden (data-only pickle expected)")

def load(fn):
    with open(ANC + fn, "rb") as f:
        return RestrictedUnpickler(io.BytesIO(f.read())).load()

results = []
def check(name, ok, detail=""):
    results.append((name, bool(ok)))
    print(f"  [{'PASS' if ok else 'FAIL'}] {name}" + (f"  -- {detail}" if detail else ""))

MAXDEN = 10**8
LO, HI, TWO25 = Fr(2486, 10000), Fr(3197, 10000), Fr(2, 25)

print("== [A] delta_final re-derived from raw dual ==")
H = load("horn_dual.pkl")
z, tag, m_ub = H["z"], H["tag"], H["m_ub"]
assert isinstance(z, list) and all(isinstance(v, float) for v in z), "z must be a float list"
rat = lambda x: Fr(x).limit_denominator(MAXDEN)   # Fraction(float) is exact binary->rational
rho   = rat(z[m_ub])
mu_hi = rat(z[tag.index("band_hi")])
mu_lo = rat(z[tag.index("band_lo")])
V = load("v2_cert_complete.pkl")
a7, a8, eps = Fr(*V["a7"]), Fr(*V["a8"]), Fr(*V["eps"])
delta_saved = Fr(*V["delta_final"])
delta_mine = HI*mu_hi - LO*mu_lo + rho - TWO25*a8 + eps
check("delta_mine == delta_saved (exact Fraction)", delta_mine == delta_saved,
      f"delta = {delta_mine} = {float(delta_mine):.10e}")
check("saved verdict flag is True", V["valid"] is True)
check("eps == 1/10^6 (the declared robust slack)", eps == Fr(1, 10**6), f"eps={eps}")

print("== [B] manifest PSD: all Gram weights nonnegative ==")
W = load("moment_gram_w.pkl")
w, sup = W["w"], W["support"]
assert isinstance(w, list) and all(isinstance(x, float) for x in w)
check(f"all {len(w)} atom weights >= 0", all(x >= 0.0 for x in w))
check(f"all {len(sup)} support weights >= 0", all(w[i] >= 0.0 for i in sup),
      f"min support w = {min(w[i] for i in sup):.3e}")
check("support indices in range and distinct",
      len(set(sup)) == len(sup) and all(0 <= i < len(w) for i in sup))
check("atoms_lab/atoms_vv lengths match support",
      len(W["atoms_lab"]) == len(sup) and len(W["atoms_vv"]) == len(sup))

print("== [C] a7 + a8 == 1 exactly (saved producer values) ==")
check("a7 + a8 == 1", a7 + a8 == 1, f"a7={a7} ({float(a7):.9f}), a8={a8} ({float(a8):.9f})")
check("a7 >= 0 and a8 >= 0", a7 >= 0 and a8 >= 0)

print("== [D] closure arithmetic (exact, no floats) ==")
d = delta_mine
check("delta < 1/20000  (= 2/(25*40^2), i.e. n=40 closes)", d < Fr(1, 20000))
check("(25/2)*40^2*delta < 1", Fr(25, 2) * 40**2 * d < 1,
      f"(25/2)*1600*delta = {float(Fr(25,2)*1600*d):.6f}")
check("(25/2)*41^2*delta >= 1  (n=41 does NOT close)", Fr(25, 2) * 41**2 * d >= 1,
      f"(25/2)*1681*delta = {float(Fr(25,2)*1681*d):.6f}")
margin = 1 - Fr(20000) * d
check("margin at n=40 is ~2.88% as claimed", Fr(287,10000) < margin < Fr(29,1000),
      f"margin = {float(margin)*100:.4f}%")
# the paper's threshold statements
check("2/(25*1600) == 5e-5 == 1/20000", Fr(2, 25*1600) == Fr(1, 20000) == Fr(5, 100000))
check("n=41 threshold 2/(25*1681) ~ 4.7591e-5", abs(float(Fr(2,25*1681)) - 4.7591e-5) < 1e-9)

print("== [E] blow-up lemma mc(G[t]) = t^2 mc(G), beta(G[t]) = t^2 beta(G) (brute force) ==")
def maxcut(n, adj):
    """adj: list of neighbor bitmasks. Exact max cut by enumerating sides of vertices 1..n-1."""
    best = 0
    for mask in range(1 << (n - 1)):
        side = (mask << 1) | 0          # vertex 0 always on side 0
        cut = 0
        for v in range(n):
            if (side >> v) & 1:
                cut += bin(adj[v] & ~side & ((1 << n) - 1)).count("1")
        if cut > best:
            best = cut
    return best

def edges(n, adj):
    return sum(bin(adj[v]).count("1") for v in range(n)) // 2

def blowup(n, adj, t):
    N = n * t
    B = [0] * N
    for u in range(n):
        for v in range(n):
            if (adj[u] >> v) & 1:
                for a in range(t):
                    for b in range(t):
                        B[u*t + a] |= 1 << (v*t + b)
    return N, B

def cyc(m):
    A = [0]*m
    for i in range(m):
        A[i] |= 1 << ((i+1) % m); A[i] |= 1 << ((i-1) % m)
    return A

def tri_free(n, adj):
    return not any((adj[u] >> v) & 1 and (adj[u] & adj[v]) for u in range(n) for v in range(u+1, n))

# all triangle-free graphs on 6 vertices (own enumeration, up to iso via canonical form)
def canon(n, adj):
    best = None
    for p in itertools.permutations(range(n)):
        bits = tuple(1 if (adj[p[i]] >> p[j]) & 1 else 0 for i in range(n) for j in range(i+1, n))
        if best is None or bits < best:
            best = bits
    return best

seen = {}
m6 = 15
for mask in range(1 << m6):
    adj = [0]*6; idx = 0
    for i in range(6):
        for j in range(i+1, 6):
            if (mask >> idx) & 1:
                adj[i] |= 1 << j; adj[j] |= 1 << i
            idx += 1
    if not tri_free(6, adj):
        continue
    k = canon(6, adj)
    if k not in seen:
        seen[k] = adj
check("count of triangle-free graphs on 6 vertices == 38 (A006785)", len(seen) == 38,
      f"got {len(seen)}")
ok_blow = True
for adj in seen.values():
    mc1 = maxcut(6, adj); e1 = edges(6, adj)
    N2, B2 = blowup(6, adj, 2)
    mc2 = maxcut(N2, B2); e2 = edges(N2, B2)
    if mc2 != 4*mc1 or e2 != 4*e1 or (e2 - mc2) != 4*(e1 - mc1):
        ok_blow = False; break
check("mc(G[2])=4mc(G), beta(G[2])=4beta(G) for all 38 triangle-free order-6 graphs", ok_blow)

ok_c5 = True
for t in (1, 2, 3):
    N, B = blowup(5, cyc(5), t)
    beta = edges(N, B) - maxcut(N, B)
    if beta != t*t:
        ok_c5 = False
check("beta(C5[t]) = t^2 for t=1,2,3 (sharpness witness)", ok_c5)
N, B = blowup(7, cyc(7), 2)
check("beta(C7[2]) = 4*beta(C7) = 4", edges(N, B) - maxcut(N, B) == 4)

print("== [F] transfer arithmetic ==")
ok_transfer = all(Fr((5*n)**2, 25) == n*n for n in range(1, 41)) and \
              all(Fr((5*n)**2, 2) * d == Fr(25, 2)*n*n*d for n in range(1, 41))
check("N=5n: N^2/25 == n^2 and N^2 delta/2 == (25/2) n^2 delta, n=1..40", ok_transfer)
ok_round = all(int(n*n + Fr(25,2)*n*n*d) == n*n for n in range(1, 41))
check("floor(n^2 + (25/2) n^2 delta) == n^2 for n=1..40 (integrality rounding)", ok_round)

print()
npass = sum(1 for _, ok in results if ok)
print(f"=== INDEPENDENT CHECK: {npass}/{len(results)} PASS ===")
print("NOT verifiable from the shipped package (requires regeneration of missing caches):")
print("  - per-state dual feasibility over the 12172 order-10 states (condition 4)")
print("  - derivation of a7/a8 from the raw dual (env table not shipped)")
print("  - envelope-row coefficients g_sigma_c and the exact moment term")
sys.exit(0 if npass == len(results) else 1)
