# Claim map — arXiv:2606.28041 (Erdős #23, gate 1)

Paper: "The Erdős n²/25 max-cut conjecture for small multiples of five, via a
per-root-MaxCut envelope and blow-up integrality", Alper Ferudun, submitted
2026-06-26 (v1), math.CO. Unreviewed preprint. 7 pages + 15 ancillary files
(4.2 MB unpacked). Sources saved under `compute23/src/` (tex + `anc/`),
producer logs and regeneration modules pulled from
`github.com/AlperTheKing/ErdosProblems` under `compute23/upstream/`.

## Exact statements

Definitions. β(G) = min edges to delete to make G bipartite = e(G) − mc(G).
a(N) = max β(G) over triangle-free G on N vertices. Erdős #23:
a(N) ≤ N²/25, sharp at C₅[N/5]; on multiples of five, a(5n) = n².

**Main theorem (Thm 1.1).** a(5n) = n² for every 1 ≤ n ≤ 40, i.e.
N ∈ {5, 10, …, 200}. Lower bound: β(C₅[n]) = n². New content is N = 25…200
(exhaustive enumeration previously known only to N = 23, OEIS A389646).

**Band theorem (Thm 3.2, the certificate).** There is an explicit rational
δ_final with

    δ_final = 21642965260808215764969346692426756225594007 /
              445715542131112582219485585645190814873007000000
            = 4.8557798001×10⁻⁵

such that d_mono(W) := 2β-density ≤ 2/25 + δ_final for every triangle-free
{0,1} step graphon W with edge density in the closed band
[LO, HI] = [1243/5000, 3197/10000] = [0.2486, 0.3197].

**Reduction (Lem 2.1 + Prop 2.2).** mc(G[t]) = t²·mc(G) hence
β(G[t]) = t²·β(G) (multilinearity: no fractional–integral cut gap); so
d_mono(W_G) = 2β(G)/N² exactly, and for N = 5n in the band,
β(G) ≤ n² + (25/2)n²δ. Integrality of β then gives β(G) ≤ n² whenever
(25/2)n²δ < 1, i.e. δ < 2/(25n²): n = 40 needs δ < 1/20000 = 5×10⁻⁵
(holds, margin 2.8844%); n = 41 needs δ < 2/42025 ≈ 4.7591×10⁻⁵ (fails:
(25/2)·41²·δ = 1.0203).

**Tails (cited).** Balogh–Clemen–Lidický arXiv:2103.14179, quoted by the
paper as "Theorem 1.3", is Theorem 2(b),(c) in arXiv v1 (a Eurocomb 2021
extended abstract with proof sketch): for n large enough, D₂(G) ≤ n²/25 when
|E(G)| ≥ 0.3197·C(n,2) or ≤ 0.2486·C(n,2). Transferred to every finite N by
blow-up (Cor 4.2); boundary densities covered by the closed band. Thresholds
and convention verified against the BCL PDF (`upstream/bcl_2103.14179.pdf`).

## Certificate format (the shipped frozen run)

The LP: state vector x ≥ 0 over the 12,172 order-10 (C₅-lifted order-9)
triangle-free band states (12,172 = # triangle-free graphs on 10 vertices,
A006785), Σx = 1, with envelope variables u_σ. Rows: band inequalities;
per-root-MaxCut envelope rows at 7 roots (107 types = # tri-free graphs on 7
vertices) and 8 roots (410 = # on 8 vertices), each row one fixed Boolean
rule c so u_σ ≤ min_c g_{σ,c}(x); rooted-Horn cuts; moment-positivity rows.
The dual is the certificate.

Shipped artifacts (`src/anc/`, SHA256-verified):

- `horn_dual.pkl` (413 KB): raw dual z (19,370 floats = 6,681 tagged rows
  [band_lo, band_hi, 317 mom, k7leg, k8leg, 6,359 env cuts, objective ρ at
  m_ub=6680] + 12,172 per-state + 517 per-type/root slacks), tag list.
  Multipliers are floats; the certificate convention rationalizes them by
  `Fraction(float).limit_denominator(10^8)`.
- `moment_gram_w.pkl` (34 KB): Gram weights w (394 floats, all ≥ 0), support
  (87 indices), and the 87 exact atom vectors vv_c (dims 7–57) with labels in
  {K0, K1, EDGE, NON}. Q = Σ w_c vv_c vv_cᵀ is PSD *manifestly* (w ≥ 0, rank-1
  sum) — no SDP solve or Cholesky rounding in the trust chain.
- `v2_cert_complete.pkl` (391 B): producer verdict — exact fractions a7, a8
  (a7 + a8 = 1), ε = 1/10⁶, δ_final, valid=True.
- `mom_term_exact.pkl` (3.7 MB): cached exact moment term, 12,172 rationals
  (~355-digit numerators/denominators).

Five dual-feasibility conditions (checked by the producer's
`complete_v2_cert.py`, frozen log in `upstream/complete_v2_cert.txt`):
(1) a7 + a8 = 1 exactly; (2) Σ_c λ_{σ,c} ≥ a7 for each of the 107 7-root
types; (3) Σ_c λ_{σ,c} ≥ a8 for each of the 410 8-root roots; (4) per-state
R_cbh(s) ≥ ⟨Q, P(s)⟩ over all 12,172 states, weakened by ε (frozen run:
min residual −8.812×10⁻⁹ ≥ −ε = −10⁻⁶); (5) δ_final = HI·μ_hi − LO·μ_lo + ρ
− (2/25)a8 + ε < 5×10⁻⁵. Caveat: the raw dual does NOT satisfy (2) as
shipped; `complete_v2_cert.py` first applies a "LEG FIX" (raises 2 deficient
type sums by adding total λ ≈ 1.36×10⁻⁸ to representative cuts) and only then
checks (1)–(5) against the fixed dual — sound, since all conditions are
re-checked after the fix, but horn_dual.pkl alone is not the final dual.

## Verification chain, step by step

1. **State generation** (order-9 tables `cp_cache.pkl` via `prove_cert.py`;
   C₅ lift `c5lift_cache.npz`; envelope/cut tables `horn_cert_state_it16.pkl`)
   — NOT shipped ("exceed arXiv ancillary limits"); the generating modules
   `prove_cert.py`, `flag_exact.py` are also not in the package but exist in
   the GitHub tree (`bridge/flagsdp/`, 563 files). Provenance split
   (established in the gate-1 addendum): `cache_n9.pkl` / `cp_cache.pkl` /
   `c5lift_cache.npz` are DETERMINISTIC combinatorial tables (geng
   enumeration, integer flag-product tensors `fs.P_sigma`, vertex-deletion
   marginal D in `c5_lift_diag.build`) — regenerated here with no LP solve
   and cross-checked; `horn_cert_state_it16.pkl` (the 6,359 envelope/Horn row
   definitions + coefficients) is saved *inside* the LP cutting-plane loop
   (`envelope_horn.py`) — certificate data from the solve, never committed to
   git, in no release: unavailable and not deterministically regenerable (the
   frozen cut set depends on solver history).
2. **Rational dual** — floats in `horn_dual.pkl` rationalized at denominator
   ≤ 10⁸; same convention used in the producer check and the gate, so the
   rationalized values are the certificate.
3. **Gram decomposition** — manifest: w_c ≥ 0 over rank-1 atoms; checkable
   from shipped data alone (checked: all 394 ≥ 0, min support weight
   9.179×10⁻⁸). Moment-row validity (⟨Q,P⟩ side) rests on Razborov
   positivity, exhibited as exact Gram forms in `g1_exact_psd.py` — not
   runnable from the package (needs `dual_cert_n9.pkl`, not shipped).
4. **Per-root envelope** — soundness d_mono ≤ U₇ is Lemma 3.1 (each rule is a
   genuine global 2-colouring on a {0,1} step graphon; envelope = type-wise
   min). Elementary graphon argument, plus author's exhaustive order-6/7 and
   zoo checks (not re-run here; the row *coefficients* live in the unshipped
   tables).
5. **Blow-up identity + integrality** — Lemma 2.1, Prop 2.2, Cor 4.2:
   elementary; fully re-verified here (exact arithmetic + brute force).
6. **Assembly** (§5): three density regimes, band closed at both endpoints,
   no coverage gap. Verified by reading; arithmetic re-checked exactly.

## What the paper does NOT claim

- No claim for n ≥ 41 (moment LP is non-deterministic, δ drifts
  ~[4.75, 4.86]×10⁻⁵ across runs; n=41 needs 4.7591×10⁻⁵, not robustly
  attained; the shipped snapshot is one frozen run).
- No claim that the LP optimum equals the band maximum (relaxation only).
- Does not resolve Erdős #23 (§7 explains the order-9/10 ceiling and reduces
  the all-n conjecture to a single self-tight invariant estimate Γ ≤ N² for
  connected B — explicitly out of scope for gate 1).
