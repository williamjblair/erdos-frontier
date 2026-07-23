# Gate-1 report — arXiv:2606.28041 reproduction (Erdős #23)

Date: 2026-07-10. Machine: Apple Silicon, single-threaded runs (≤ 2 cores per
budget; total compute: ~20 s initial pass + ~12 min regeneration addendum).
All exact checks in rational arithmetic.

## FINAL VERDICT (after condition-4 addendum): STILL-PARTIAL — sharply narrowed

After the addendum (see "Condition-4 addendum" section below), every
deterministically derivable ingredient of the certificate chain is verified —
most of it bit-for-bit — including the COMPLETE moment side of condition 4
over all 12,172 states (full coverage, not sampled). The untrusted remainder
is exactly one object: the 6,359 envelope/Horn row coefficient vectors
(`horn_cert_state_it16.pkl`), an LP-solve product never published anywhere
(arXiv package, GitHub tree, git history, and releases all checked — zero
hits). Conditions (2), (3) and the R_cbh side of condition (4) rest on those
rows and are attested only by the producer's frozen log. Closing this would
require the author to publish that one file; regenerating it means re-solving
the LP (out of scope, and non-reproducible by the paper's own
non-determinism admission).

## Initial-pass verdict: PARTIALLY REPRODUCED

Everything checkable from the shipped ancillary package was verified, both by
running the author's verifier and by an independent from-scratch checker
(21/21 PASS), and the brute-force ground truth was reproduced exactly with an
independent implementation. The single most load-bearing computational step —
per-state dual feasibility over the 12,172 order-10 states (condition 4) —
is NOT verifiable from the package as shipped: the state tables and two
required Python modules are absent (the modules exist in the author's GitHub
tree; the tables would have to be regenerated, which is certificate
*generation* and out of gate-1 scope). For that step we have only the
producer's frozen log. The envelope-row and moment-row *semantics* (steps 3–4
of the chain) are likewise not independently checkable from shipped data.

## Chain status per step

| Step | Status | Evidence |
|---|---|---|
| Package integrity | VERIFIED | `shasum -c SHA256SUMS`: all 13 files OK; pickles audited opcode-level, pure data (no globals) |
| State generation (order-9/10 tables, C₅ lift) | initial: NOT CHECKABLE → addendum: REGENERATED + CROSS-CHECKED | deterministic tables (`cache_n9`, `cp_cache` contents, `c5lift_cache`) regenerated from fetched GitHub code with no LP solve; validated by exact edge-count identity (12,172/12,172), own-code recounts (S1), labelg-based D rebuild (S2) — see addendum |
| Rational dual: δ_final re-derivation from raw z | VERIFIED INDEPENDENTLY | my `independent_check.py` [A]: δ = 4.8557798001×10⁻⁵ re-derived from `horn_dual.pkl` floats under the declared rationalization, equals saved fraction bit-for-bit |
| Gram decomposition manifest-PSD (w_c ≥ 0) | VERIFIED INDEPENDENTLY | [B]: all 394 atoms ≥ 0; 87 support atoms ≥ 0 (min 9.179×10⁻⁸); structure sane |
| a7 + a8 = 1, a7, a8 ≥ 0 | VERIFIED (values not re-derivable) | [C]: exact on saved fractions; but a7 := 1 − a8 by construction, and per-type/per-root sums (conditions 2–3) need the unshipped env table |
| Per-state residual (condition 4, 12,172 states) | addendum: mom side VERIFIED bit-for-bit (12,172/12,172); R_cbh side NOT REPRODUCED — producer log only | ⟨Q,P(s)⟩ recomputed exactly from regenerated tables + shipped Gram atoms, equals shipped `mom_term_exact.pkl` on every state. R_cbh needs the unpublished env rows; frozen log `upstream/complete_v2_cert.txt`: min residual −8.812×10⁻⁹ ≥ −ε = −10⁻⁶. The shipped "independent gate" merely reads the saved `valid=True` flag for this condition |
| Threshold/closure arithmetic (n ≤ 40 closes, 41 fails) | VERIFIED INDEPENDENTLY | [D]: δ < 1/20000 exact; (25/2)·1600·δ = 0.971156 < 1 (margin 2.8844%, paper says 2.88%); (25/2)·1681·δ = 1.020321 ≥ 1 |
| Blow-up identity β(G[t]) = t²β(G) | VERIFIED INDEPENDENTLY | proof read (multilinearity argument is correct and standard); brute-forced for all 38 triangle-free order-6 graphs at t=2, C₅[t] t=1..3 (β = t²), C₇[2] |
| Graphon transfer d_mono(W_G) = 2β/N² | VERIFIED by reading | the same no-fractional-gap argument as Lemma 2.1 gives measurable-colouring optimum = integral optimum on step graphons; sound |
| Tails (BCL) | CITATION VERIFIED, proof external | BCL arXiv v1 Theorem 2(b),(c): thresholds 0.3197/0.2486 · C(n,2), "for n large enough" — matches use. Note: cited as "Theorem 1.3" (numbering differs) and BCL arXiv v1 is a Eurocomb *extended abstract* with a proof sketch (flag-algebra SDP); the tails carry their own unverified computational burden |
| Assembly (3 regimes, closed band, no gap) | VERIFIED by reading + exact arithmetic | boundary densities in closed band; [F] transfer identities for all n = 1..40 |
| Brute-force ground truth | REPRODUCED INDEPENDENTLY | own C checker (own g6 decoder + Gray-code max cut) vs paper: in-band max d_mono n=9..12 = 0.049383/0.040000/0.049587/0.055556 (paper: 0.0494/0.0400/0.0496/0.0556) — exact match; author's `brute_dmono.py` (geng path patched) agrees on n=9,10 |
| OEIS cross-check | VERIFIED | my a(N), N=5..12 = 1,1,1,2,2,4,4,5 match A389646 b-file exactly; a(5)=1², a(10)=2² as the paper cites; counts 14/38/107/410/1897/12172/105071/1262180 match A006785 |

Author-runnable scripts from the package: `step1_v2_independent_gate.py`
(PASS, 0.1 s — log `logs_step1_gate.txt`) and `brute_dmono.py` (needs external
nauty geng + path patch — log `logs_author_brute_n9_10.txt`). Everything else
(`complete_v2_cert.py`, `moment_gram_lp.py`, `moment_gram_exact_verify.py`,
`g1_exact_psd.py`, `g1_graphon_density.py`) fails on missing imports/caches.

## Discrepancies and caveats (noted, not over-weighted)

1. **The "independent gate" is weaker than its name.** For condition 4 it
   only reads the producer's saved boolean; a7/a8/ε are taken from the
   producer's pickle, and condition 2 is checked on values the producer
   constructed to satisfy it. Its genuinely independent content: δ formula
   re-derivation from raw z, w ≥ 0, threshold comparison. My checker
   reproduces exactly that independent content (plus the elementary layer).
2. **Raw dual needs a post-solve "LEG FIX".** `horn_dual.pkl` violates
   condition 2 for 2 of 107 types; `complete_v2_cert.py` repairs it by adding
   λ ≈ 1.36×10⁻⁸ before checking. Sound (all conditions re-checked after),
   but the shipped dual is not final as-is and the gate doesn't see this.
3. Stale text in the gate docstring: "δ < 5e-5 ⇒ n ≤ 41, N ≤ 205" and
   "extended from N ≤ 55 to N ≤ 205" — wrong; δ < 5×10⁻⁵ gives n = 40 and the
   printed output/paper correctly say N ≤ 200.
4. Paper §6 says Gram support "77 atoms"; the frozen `moment_gram_w.pkl` has
   **87**. Paper §6 says worst residual "−1.02×10⁻⁸"; frozen log says
   −8.812×10⁻⁹. Both consistent with the admitted non-determinism of the
   moment LP — the paper text describes a different run than the frozen
   snapshot it ships.
5. ε = 10⁻⁶ is a flat robustness bump added to δ (not the ~10⁻⁸ residual
   itself); harmless — it only weakens the bound, and is included in δ_final.
6. BCL citation numbering ("Theorem 1.3" vs Theorem 2 in arXiv v1) and its
   extended-abstract status (see table).
7. `brute_dmono.py` hardcodes a Windows `geng.exe` path; nauty not included.
8. README claims the caches are "regenerable from the scripts", but the
   package lacks `prove_cert.py`/`flag_exact.py` (GitHub-only), and the claim
   is only TRUE for the deterministic tables (addendum regenerated them). It
   is FALSE for `horn_cert_state_it16.pkl`: the env rows come out of the LP
   loop, whose cut selection is solver-history dependent and, per the
   author's own note, non-deterministic — a rerun produces a different frozen
   certificate, not this one.

None of these touch the verified arithmetic; items 1–2 are the reasons the
verdict is "partially" rather than "fully" reproduced.

## What I ran (artifacts in compute23/)

- `independent_check.py` — from-scratch checker, 21/21 PASS, 6 s
  (`logs_independent_check.txt`): restricted unpickler; δ re-derivation;
  w ≥ 0; exact closure arithmetic incl. margins; brute-force blow-up lemma;
  transfer/rounding identities for n = 1..40.
- `brute_check.c` — independent C ground truth, n = 5..12 via
  `geng -q -t n | ./brute_check n` (n=12: 4.9 s single-threaded).
- Author's gate + author's brute script (patched geng path), logs saved.
- `upstream/` — producer frozen logs, all generator modules
  (`prove_cert.py`, `flag_exact.py`, `flag_sdp.py`, `flag_cutgen.py`,
  `flag_localizer.py`, `flag_localcut.py`, `build_cache.py`,
  `c5_lift_diag.py`, `envelope_horn.py`, …), BCL PDF; GitHub provenance in
  `PROVENANCE.txt` (commit + blob SHAs).
- `regen/` — addendum artifacts: `regen_build.py` (deterministic
  regeneration + bit-for-bit moment comparison; logs `regen_build*.log`),
  `spotcheck.py` (own-code recounts + labelg D rebuild; logs
  `spotcheck_s1.log`, `spotcheck_s2.log`), `run_author_verifier.py`
  (failure-isolation demo; log `run_author_verifier.log`),
  `my_mom_term_exact.pkl` (regenerated moment term, equals shipped),
  regenerated caches `my_moments_n9.pkl` (87 MB), `cache_n9.pkl` (87 MB),
  `c5lift_cache.npz` (2.4 MB).

## Condition-4 addendum (regeneration push, coordinator request)

Goal: complete condition 4 — R_cbh(s) ≥ ⟨Q,P(s)⟩ over the 12,172 states —
distinguishing deterministic combinatorial tables (regenerable, allowed) from
LP/dual products (off-limits). All work in `compute23/regen/`; fetched code
in `compute23/upstream/` with GitHub provenance (`upstream/PROVENANCE.txt`:
commit 5ca9b7d7fe0d, per-file blob SHAs).

### 1. Availability sweep (exhaustive)

- GitHub tree at HEAD (recursive, not truncated): **zero** `.pkl`/`.npz`/
  `.npy` files anywhere in the repo. No releases. Git history for
  `horn_cert_state_it16.pkl`, `horn_Rcbh_exact.pkl`, `c5lift_cache.npz`,
  `cache_n9.pkl`, `dual_cert_n9.pkl`: **zero commits ever touched these
  paths** — the caches were never published. Fetch was therefore impossible;
  only regeneration remained.
- Provenance split confirmed from the fetched generators:
  `cache_n9.pkl` (`build_cache.py`: geng enumeration + integer flag-product
  tensors `fs.P_sigma` — pure counting), `cp_cache.pkl` (only `ns0`, `dedge`
  consumed by the verifier — trivial combinatorics), `c5lift_cache.npz`
  (`c5_lift_diag.build`: D_{H,J} = (1/10)|{v : J−v ≅ H}|, vertex-deletion
  marginal — pure counting) are DETERMINISTIC.
  `horn_cert_state_it16.pkl` (env rows) is written *inside* the LP
  cutting-plane loop (`envelope_horn.py`, iteration state at it=16) — an
  LP-solve product. `horn_dual.pkl` stores only category index lists
  (k7cuts: 3,643, horncuts: 2,716, k8cuts: 0 — total 6,359 rows) with **no
  coefficients and no cut identities**, so the rows cannot be reconstructed
  from the shipped dual either.

### 2. Deterministic regeneration (no LP solved anywhere)

`regen/regen_build.py`, author pipeline (only patch: geng path; nauty 2.9.3
vs author's 2_8_9), single-threaded, ~11 min total:

- Order-9 tables: 1,897 states; moment blocks K0/K1/EDGE/NON with flag
  dimensions 7/35/34/57 — exactly matching the shipped Gram atom dimensions.
- Lift D: nnz = 94,703 over 1,897 × 12,172 (built in 36 s).
- Exact sanity: 45·(Dᵀ·dedge₉)[s] equals the edge count of state s from my
  own independent graph6 decode, as exact rationals, for **all 12,172
  states** — the lift and the band row data are mutually consistent.

### 3. Moment side of condition 4: FULLY VERIFIED, bit-for-bit

Recomputed ⟨Q,P(s)⟩ exactly (same rationalization conventions as
`complete_v2_cert.py`: w_c and vv_c at denominator 10⁶, D entries exact) from
the REGENERATED tables + the SHIPPED 87 Gram atoms:
**my moment term equals the shipped `mom_term_exact.pkl` on 12,172 / 12,172
states, exact-Fraction equality** (`regen/regen_build2.log`, ~5.5 min;
output banked as `regen/my_mom_term_exact.pkl`). This is complete coverage —
the coordinator's sampling fallback was not needed.

### 4. Independent spot checks of the regenerated tables (own code)

`regen/spotcheck.py`, seed 20260710, reproducible:
- [S1a] K0 count tensors recounted with my own implementation (own
  root-fixed canonical form, own σ-induction test, own disjoint-pair loop)
  for **all 1,897 states**: 0 mismatches.
- [S1b] 200 seeded (label, state) pairs across K1/EDGE/NON, full-matrix
  recounts: 0 mismatches.
- [S2] 500 seeded D columns rebuilt from scratch (own g6 decode/encode,
  vertex deletions canonized by nauty `labelg` — a third-party canonizer):
  0 mismatches; T₉ index alignment with the author-pipeline enumeration is
  1:1 (also confirms geng ordering stability across nauty versions).

### 5. Author's verifier: failure isolated to one file

With ALL deterministic inputs regenerated and supplied (`cache_n9.pkl`,
synthesized `cp_cache.pkl` carrying the regenerated ns0/dedge,
`c5lift_cache.npz`, plus the shipped certificate pickles),
`complete_v2_cert.py` proceeds through its cache loads and stops at exactly
line 20: `FileNotFoundError: horn_cert_state_it16.pkl`
(`regen/run_author_verifier.log`). Conditions (2), (3) and the R_cbh
assembly in condition (4) all require that file's 6,359 (coefficients,
indices) rows.

### Addendum outcome

| Condition | Status after addendum |
|---|---|
| (1) a7 + a8 = 1 | verified exactly (initial pass) |
| (2) per-type λ sums ≥ a7 | UNTRUSTED — needs env rows (frozen log only) |
| (3) per-root λ sums ≥ a8 | UNTRUSTED — needs env rows (frozen log only) |
| (4) resid[s] = R_cbh[s] − mom[s] ≥ −ε | mom[s]: VERIFIED bit-for-bit, all 12,172 states. R_cbh[s]: UNTRUSTED — needs env rows |
| (5) δ_final formula and δ < 5×10⁻⁵ | verified exactly (initial pass) |

The near-tight-residual analysis the coordinator suggested (all states within
10× of the frozen minimum residual) is not possible without R_cbh; noted
explicitly rather than approximated. Consistency evidence that does exist for
the R side: `horn_dual.eta` = 4.755705904754391×10⁻⁵ matches the exact
δ(pre-moment) = 125361431662/2636021532814425 in the producer's
`horn_Rcbh_exact.txt` log, and ρ − (2/25)·a8 + ε reproduces δ_final exactly
with μ_hi = μ_lo = 0 as that log records — the shipped dual, the frozen logs,
and the verdict pickle all cohere. Coherence is not verification; the row
data itself remains the trust gap.

## Formalizability scoping (checker only, not the flag algebra)

Target shape (matches this repo's decide-certificate idioms, no
`native_decide`):

```
-- elementary layer (provable outright, no data)
theorem blowup_mc  : mc (G.blowup t) = t^2 * mc G            -- multilinearity
theorem blowup_bip : β (G.blowup t) = t^2 * β G
theorem integrality (h : (β G : ℚ) ≤ n^2 + (25/2)*n^2*δ)
    (hδ : (25/2)*n^2*δ < 1) : β G ≤ n^2

-- certificate layer (kernel computation on concrete rational data)
theorem cert_ok : CheckCert certData = true                  -- by decide-style eval
-- CheckCert = conditions (1)–(5): a7+a8=1, leg sums, per-state resid ≥ −ε,
--             δ_final formula, δ_final < 1/20000

-- trust boundary (stated hypotheses, NOT formalized now)
-- (H1) envelope/Horn/moment row validity for triangle-free graphons
--      (Lemma 3.1 + Razborov positivity)  ⇒  CheckCert ⇒ band bound
-- (H2) BCL tails (asymptotic) + blow-up transfer

theorem main (H1) (H2) : ∀ n ≤ 40, a (5*n) = n^2
```

Cost estimates:

- **Elementary layer** — small. Blow-up lemma: SimpleGraph blow-up +
  one-coordinate-at-a-time rounding of fractional cuts (pure convexity, no
  measure theory needed if the theorem is phrased finitely); ~300–600 lines
  with Mathlib. Integrality/threshold/transfer: `norm_num`-level; the exact
  δ is a 44/48-digit fraction — trivial for the kernel. The graphon can be
  eliminated from the *statement* entirely by phrasing H1's conclusion
  finitely ("∀ triangle-free H in band, 2β(H)/|H|² ≤ 2/25 + δ"), which is
  exactly what Cor 4.2-style blow-up transfer needs.
- **Certificate data size** — shipped compact form: 6,681 rationalized
  multipliers (denominators ≤ 10⁸) + 87 Gram atoms (dims ≤ 57) + 12,172
  moment-term rationals at ~355 digits each (~9 MB of digits) + 12,172
  R_cbh rationals. As Lean source ≈ 15–30 MB. Fine as a bank file.
- **Kernel work, thin checker** (take R_cbh and mom-term as certificate
  data; check w ≥ 0, a7+a8=1, resid[s] = R_cbh[s] − mom[s] ≥ −ε, δ formula,
  δ < 1/20000): ~13k comparisons + ~13k subtractions of ~350-digit rationals
  ≈ 10⁵–10⁶ bignum ops — comfortably `decide`-feasible with a
  common-denominator integer encoding (the repo's existing idiom). Days of
  work, not months. BUT the thin checker inherits R_cbh/mom-term as data, so
  it certifies only the final inequality assembly, not the row aggregation.
- **Kernel work, faithful checker** (re-derive R_cbh from the 6,359 envelope
  rows and mom-term from the 87 atoms through the order-9→10 lift). The
  addendum gives concrete anchors for the mom half: the deterministic tables
  are 1,897 states × four integer tensors (7²+35²+34²+57² entries per state;
  87 MB as a Python pickle, mostly int64 padding — the nonzero content is far
  smaller), the lift D has 94,703 rational entries, and the full exact mom
  recomputation was ~10⁷ big-rational multiply-adds (5.5 min in Python
  `fractions`). That half is borderline-feasible in-kernel with aggressive
  integer common-denominator staging. The R_cbh half additionally needs the
  6,359 env coefficient rows — data that does not exist publicly, so a
  faithful checker is BLOCKED on the author regardless of engineering. If the
  author publishes the env rows (or better, R_cbh with per-row provenance),
  the thin checker upgrades to condition-(2)/(3)/(4) coverage at roughly
  double its cost.
- Formalizing H1 itself (envelope soundness + Razborov positivity) is graphon
  /flag-algebra territory — out of scope by instruction, and Mathlib has no
  graphon layer; the finite reformulation above keeps it a clean, honest
  hypothesis.

## Hard stop

Per instructions: no LP extension attempted, no connected-B/Γ-invariant work
started.
