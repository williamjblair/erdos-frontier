# Gate 2 — Erdős #23: structural analysis of the Γ ≤ N² obstruction

Paper: arXiv:2606.28041 §7 ("The obstruction to all n").  Scope per memo:
analysis only, no LP/flag work, no attempt at the full conjecture.  Machine:
≤ 2 cores, all runs single-threaded and `nice -19`; total compute ≈ 12 min
(dominated by two n=13 sweeps).  **Every counterexample / kill claim below
is machine-verified in exact integer or rational arithmetic**; floating
point was used only to *locate* certificates, never to certify them.
Scripts and logs in `compute23/gate2/` (inventory in §6).

Headline results:

1. The obstruction is restated self-contained (§1); all side conditions
   derived and machine-asserted across **49.7 million** max-cut instances
   (every maximum cut of every connected triangle-free graph, 5 ≤ N ≤ 13):
   zero violations of the side conditions, zero violations of Γ ≤ N².
2. The equality set is **larger than the paper suggests**: not just
   balanced C₅-blow-ups but *all odd cycles* C_{2k+1} and *all balanced
   odd-cycle blow-ups* C_{2k+1}[q] are tight.  Within N ≤ 13 the equality
   cases are exactly C₅, C₇, C₉, C₁₁, C₁₃, C₅[2]  (§4).
3. Block decomposition (§2): two unconditional reductions are theorems; the
   scalar-potential route to the cut-vertex case is **provably dead**
   (explicit exact obstructions), but the *true* cut-vertex composition
   inequality survives everything, and a new single-block lemma **RL**
   (§2.5) — machine-verified on all enumerated one-stub rooted instances —
   implies its k=1 case by pure algebra.  RL is the recommendation (§5).
4. Candidate scoreboard (§3): the local-load (L²) strengthening, the
   path-packing (L¹) lemma, and the Hölder product form are all **killed**
   with small exact witnesses (n = 8, 12, 9 respectively); the
   effective-resistance variant is structurally insufficient; convex path
   functionals are pinned to the quadratic.  A by-product: a 12-vertex
   triangle-free graph with **β > e/5** (§3.2) — the C₅/Petersen extremal
   ratio fails already at n = 12 once Δ = 4.

---

## 1. The restated obstruction (task 1)

### 1.1 Setup

All graphs finite and simple.  For G on N vertices, β(G) = e(G) − mc(G) is
the bipartization number.  A **valid instance** is a pair (G, χ) where G is
triangle-free and χ : V(G) → {0,1} attains the maximum cut.  Write

* M  = monochromatic edges of χ  (|M| = β(G), see S0),
* B  = bichromatic edges (the *cut graph*, a spanning subgraph),
* d_B(u,v) = graph distance in B.

**Conjecture Γ (the paper's obstruction, restated).**  For every valid
instance with B connected,

    Γ(G,χ)  :=  Σ_{uv ∈ M} ( d_B(u,v) + 1 )²   ≤   N².

Equivalently (each M-edge uv closes with a shortest B-path into an odd
cycle C_uv of length d_B(u,v)+1 in G): *the sum of squared lengths of
shortest odd cycles through the monochromatic edges is at most N².*

### 1.2 Side conditions — each derived, then machine-verified

**(S0) |M| = β(G).**  χ is a maximum cut, so #monochromatic = e − mc = β.

**(S1) B is bipartite** with parts χ⁻¹(0), χ⁻¹(1), by construction; for
connected B this is its unique bipartition (up to swap), so χ is
recoverable from B alone.

**(S2) Flip characterisation of maximality.**  Every 2-colouring of V is
obtained from χ by flipping a set T; the cut changes by
e_M(δT) − e_B(δT), where δT = edges with exactly one endpoint in T.  Hence

    χ max cut  ⟺  ∀ T ⊆ V :  e_M(δT) ≤ e_B(δT).

This is the *complete* list of usable constraints (with triangle-freeness):
a pair (M, B), B bipartite, arises from a valid instance iff S2 holds and
B ∪ M is triangle-free.  Verified directly on C₅[2] over all 2⁹ flips
(`verify_c5_blowup.py`, check [6]).

**(S3) Local degrees** (T = {v}): d_M(v) ≤ d_B(v) for every vertex.
Machine-asserted on all 49.7M instances.

**(S4) Parity.**  uv ∈ M means χ(u) = χ(v); in bipartite B *every* u–v
path has even length.  So d_B(u,v) is even.  Machine-asserted everywhere.

**(S5) d_B(u,v) ≥ 4.**  d_B ≠ 0 (u ≠ v), ≠ 2 (a common B-neighbour w would
close the triangle uwv with the M-edge uv).  With S4: d_B ≥ 4, so

    (d_B(u,v)+1)² ≥ 25   for every M-edge.        Machine-asserted.

**(S6/S7′) Connectivity is free.**  For *any* maximum cut of *any* graph:
flipping a whole connected component C of B turns every G-edge between C
and V∖C — all monochromatic, since B-edges never leave a B-component —
into a cut edge; maximality forces there to be none.  Hence **every
B-component is a union of G-components**, and an isolated B-vertex is an
isolated G-vertex.  Consequently *G connected ⟹ B connected and spanning,
for every maximum cut*: the hypothesis "B connected" in Conjecture Γ is
exactly "G connected".  Machine-asserted on all 49.7M instances — B came
out connected and spanning every single time.

### 1.3 Why Conjecture Γ implies Erdős #23

Let G be triangle-free on N vertices, χ a maximum cut.  By S6/S7′ the
G-components G₁,…,G_r (sizes N_i) carry the whole structure, and the
restricted colourings are maximum cuts of the components (a better
component cut would improve χ).  Conjecture Γ per component plus S5:

    25·|M_i| ≤ Γ_i ≤ N_i²   ⟹   β(G) = Σ|M_i| ≤ Σ N_i²/25 ≤ N²/25.

All steps elementary.  Note Γ ≤ N² is *strictly stronger* than β ≤ N²/25
per instance unless every M-distance equals 4.

### 1.4 Exact sanity checks (`verify_c5_blowup.py`, all PASS)

* **C₅[q], q = 1..4** (N = 5q): the blow-up cut (V₁∪V₃ | V₂∪V₄∪V₅) is a
  maximum cut (brute force), M = V₄×V₅ (|M| = q²), every d_B = 4, and
  **Γ = 25q² = N² exactly** — the expected equality, verified.
* **All** maximum cuts of C₅[1] (5 cuts) and C₅[2] (15 cuts) give Γ = N².
* **Odd cycles C₅…C₁₃**: every maximum cut (N of them) has B = Hamiltonian
  path, one M-edge at distance N−1, Γ = N² — a *second* equality family.
* **C₇[2]** (N=14): blow-up cut is max, |M| = 4, all d_B = 6,
  Γ = 4·49 = 196 = N² — equality *beyond* C₅-blow-ups.  (In general
  β(C_{2k+1}[q]) = q² by the paper's own blow-up identity, all M-distances
  are 2k in the blown path, so Γ = q²(2k+1)² = N² for every balanced
  odd-cycle blow-up: the (d+1)² weight is exactly calibrated so that longer
  odd cycles, which waste β, are compensated by longer B-distances.)
* **Unbalanced blow-ups are strict**: C₅[2,1,1,1,1] (max Γ = 25 < 36),
  C₅[3,2,2,2,2] (100 < 121), C₅[2,2,2,2,1] (50 < 81), over *all* their
  maximum cuts.

### 1.5 Exhaustive verification, N ≤ 13 (`gamma_search.c`)

Every maximum cut of every connected triangle-free graph (geng -q -c -t):

| N | graphs | max-cut instances | with M≠∅ | Γ-equality | Γ-CEX |
|---|--------|------------------|----------|-----------|-------|
| 5 | 6 | 10 | 5 | 5 (= C₅) | 0 |
| 6 | 19 | 25 | 8 | 0 | 0 |
| 7 | 59 | 97 | 53 | 7 (= C₇) | 0 |
| 8 | 267 | 462 | 280 | 0 | 0 |
| 9 | 1,380 | 2,649 | 1,919 | 9 (= C₉) | 0 |
| 10 | 9,832 | 20,206 | 16,174 | 15 (= C₅[2]) | 0 |
| 11 | 90,842 | 199,191 | 173,593 | 11 (= C₁₁) | 0 |
| 12 | 1,144,061 | 2,640,775 | 2,427,995 | 0 | 0 |
| 13 | 19,425,052 | 46,831,869 | 44,590,139 | 13 (= C₁₃) | 0 |

Zero counterexamples; zero side-condition violations; equality graphs
verified structurally (2-regular ⟹ odd cycles; the n=10 graph is
4-regular with the 5 twin-pairs of C₅[2]).

### 1.6 The paper's "different even lengths" hard case, made precise

By S4 *all* u–v paths in B are even for uv ∈ M, so the phrase cannot mean
parity mixing.  Two readings:

(a) *per-pair*: some uv ∈ M is joined by simple B-paths of two different
even lengths.  This cannot be the discriminator: it already happens inside
the extremal C₅[q] for q ≥ 2 (zig-zag paths of length 6 beside the
geodesics of length 4).

(b) *per-instance* (**the reading supported by our data**): the multiset of
M-distances is non-constant ("mixed-length instances").  Every candidate
killed in §3 died exactly at mixed-length or forced-hub witnesses —
{4,4} with a common hub (C3, n=8), {6,4} (C9, n=9), {6,4,4,4} (C9, n=12) —
while every candidate holds with equality on both constant-length families.
The hard case is the regime where different M-edges use different even
distances, because the two equality families pin any weighting from both
ends (§3.5) and the mixed instances interpolate between them.

---

## 2. Minimal-counterexample structure: cut vertices and bridges (task 2)

Throughout: (G, χ) a counterexample to Conjecture Γ minimizing N; B its
cut graph (connected, spanning, by S7′ since G must be connected).

### 2.1 Theorem (leaf reduction) — unconditional

*In a minimal counterexample every B-leaf is an endpoint of an M-edge.*
Proof: if u is a B-leaf with no M-edge, delete it.  The restriction of χ is
a maximum cut of G−u (a better cut of G−u extends to a better cut of G by
placing u opposite its B-neighbour); B−u stays connected and spanning; no
shortest path routes through a leaf, so Γ is unchanged while N drops —
a smaller counterexample.  ∎  (By S3, leaves carry at most one M-edge.)

### 2.2 Theorem (crossing-free cut vertices die) — unconditional

*In a minimal counterexample, for every cut vertex w of B and every split
V = V₁ ∪ V₂, V₁∩V₂ = {w}, of B at w, some M-edge crosses (one endpoint in
V₁∖{w}, one in V₂∖{w}).*  Proof: suppose not.  For T ⊆ V₁∖{w} the global
flip condition restricts (B-edges of δT lie in B₁ = B[V₁], M-edges of δT
in M₁₁), and flips of G[V₁] with w ∈ T are equivalent to flips of the
complement inside V₁; so (G[V₁], χ|V₁) is a valid instance, B₁ connected
and spanning (every component of B−w attaches to w by an edge), N₁ < N.
Distances inside V_i agree with d_B (paths cannot shortcut through the
other side without repeating w).  By minimality Γ₁₁ ≤ N₁², Γ₂₂ ≤ N₂², and
with no crossing edges Γ = Γ₁₁ + Γ₂₂ ≤ N₁² + N₂² ≤ (N₁+N₂−1)² = N², using
N₁, N₂ ≥ 2.  Contradiction.  ∎

Bridges: a bridge with ≥ 2 vertices on both sides yields a cut vertex,
handled above / below; a pendant bridge is the leaf case.

### 2.3 Rooted instances and an exact equivalence

To attack cut vertices *with* crossing edges, cut the instance at w.  A
**rooted instance** R = (B, M, w, σ) is a connected bipartite B on n
vertices, internal M (same side, d_B ≥ 4, B ∪ M triangle-free), a marked
vertex w, and stub counts σ : V∖{w} → ℕ (σ(u) = number of crossing M-edges
cut at w with near endpoint u), subject to the **rooted flip condition**

    ∀ T ⊆ V∖{w} :  e_M(δT) + σ(T) ≤ e_B(δT).

**Theorem (equivalence).**  Gluing two rooted instances at w (pairing
stubs into crossing edges u—v with d₁(u,w)+d₂(w,v) even and ≥ 4, no
multi-edges, no new triangles) yields a valid composite instance iff both
halves are rooted-valid; every valid instance whose B has a cut vertex
arises this way; crossing distances add: d_B(u,v) = d₁(u,w) + d₂(w,v).
Proof sketch: (⟸) for T ∌ w (WLOG), T = T₁ ⊔ T₂; each crossing edge
contributes to e_M(δT) at most its stub memberships; the sum of the two
rooted conditions dominates the composite condition.  (⟹) restrict T to
one side; a crossing edge's far endpoint is outside T, contributing
exactly σ(T).  ∎ — spot-verified: every composite assembled in Stage C of
`rooted_search.py` had its glued colouring confirmed as a maximum cut by
brute force (the "NOT MAX CUT" branch never fired).

Structural corollary (Gale–Hoffman, single commodity): with M = ∅ the
rooted condition is exactly the max-flow cut condition for routing σ to
sink w with unit edge capacities, so **the crossing M-edges at a cut
vertex extend to edge-disjoint B-paths into w** (integrally).  The
crossing structure at an articulation is a genuine edge-disjoint bundle of
half-odd-cycles.  (This single-commodity truth is also why the
multicommodity candidate C2 in §3 looks true for so long.)

### 2.4 The potential/superadditivity route is provably dead

The natural per-block potential (Minkowski / second-order-cone form): give
stub j a split parameter t_j ∈ [0,1] and set
‖v_R(t)‖² = Γ_int + Σ_j (d_j + t_j)²; then for any composite and any
splits with t¹_j + t²_j = 1,

    √Γ_comp  ≤  ‖v₁(t¹)‖ + ‖v₂(t²)‖         (Minkowski),

so the cut-vertex induction closes if each half satisfies
Γ_int + Σ(d_j+t_j)² ≤ (n−1+s)² with s-budgets summing to 1.

Enumerating **all** valid rooted instances with n_B ≤ 9, |M| ≤ 2 internal
edges, k ≤ 2 stubs — 478,000 instances, 165 distinct signatures
(n, Γ_int, D) — shows (`rooted_search.py`, `logs_rooted.txt`):

* **D′ (fixed t = ½) is false.**  Three violating signatures, e.g. the
  hand-predicted K₂,₂ with a double stub on the antipode of w:
  Ψ = 2·(2+½)² = 25/2 > 49/4 = (4−½)² (exact Fractions).  Also
  (6, 25, (2,)) and (7, 25, (4,)) — a C₅ inside the block plus one stub.
* **No choice of splits rescues it.**  Fifteen signature pairs have
  min_t [‖v₁(t)‖ + ‖v₂(1−t)‖] > N.  Two of them exactly, by algebra:
  (3,0,(2)) × (7,25,(4)) needs √(25+(4+t)²) ≤ 6+t ⟺ t ≥ 5/4 — infeasible
  on [0,1]; the (4,0,(2,2)) self-pair gives ‖v₁‖+‖v₂‖ ≡ 5√2 and
  (5√2)² = 50 > 49 = N².  The remaining 13 were flagged numerically
  (convex 1–2-dim minimization, margins ≥ 0.005 ≫ grid error).  Crucially,
  **every realizable flagged pair assembles into a composite that
  satisfies Γ ≤ N² with slack** (e.g. (3,0,(2))×(7,25,(4)): potential
  bound 9.07 > 9 = N, but Γ_comp = 74 ≤ 81; all composites verified by
  exact brute force).  The loss is intrinsic: Minkowski is tight only for
  proportional vectors, and validity prevents the halves from being
  simultaneously extremal in the aligned direction — information invisible
  to any per-block aggregation of (Γ_int, stub distances) into one scalar.

**Verdict: block decomposition through a one-scalar-per-block potential in
the boundary data (Γ_int, D) is impossible.**  These are explicit,
machine-checked obstructions, not heuristics.

### 2.5 What survives: the true composition inequality, and lemma RL

By the equivalence (2.3), the cut-vertex case of Conjecture Γ is *exactly*
the **pair inequality**: for all valid rooted R₁, R₂ with stubs matched by
a bijection π,

    Γ₁ + Γ₂ + Σ_j ( d¹_j + d²_{π(j)} + 1 )²  ≤  ( n₁ + n₂ − 1 )².

Tested exactly over all 2,463 compatible signature pairs from the n_B ≤ 9
enumeration (stage B′): **one violation — and it is not realizable.**  The
signature (4,0,(2,2)) is realizable *only* with both stubs on a single
vertex (the K₂,₂ antipode; the star and path variants fail the rooted flip
condition), so the "violating" self-pairing (lhs 50 > 49) would need a
doubled edge and is blocked.  Every realizable pair satisfies the
inequality; the 19 equality pairs are **exactly path × path** (= the odd
cycles).  Composites of total size ≤ 13 also hold exhaustively via §1.5.

For k = 1 (one crossing edge) the pair inequality follows by pure algebra
from a *single-block* statement.  Let s := n − 1 − d ≥ 0 (the block's
vertex slack over its stub geodesic) and p(d) := least admissible partner
distance (parity match, sum ≥ 4): p(1)=3, p(2)=2, p(3)=1, p(even ≥ 4)=2,
p(odd ≥ 5)=1.

**Lemma RL (proposed).**  For every valid rooted instance with exactly one
stub, at distance d from w:

    Γ_int  ≤  s·(2d + 2 + s) + 2·s·p(d).

**RL ⟹ pair inequality (k=1):**  with s_i = n_i − 1 − d_i,

    (n₁+n₂−1)² − (d₁+d₂+1)²
      = s₁(2d₁+2+s₁) + s₂(2d₂+2+s₂) + 2s₁d₂ + 2s₂d₁ + 2s₁s₂,

and RL bounds Γ_i by the i-th bracket plus 2s_i·p(d_i) ≤ 2s_i·d_{3−i}.  ∎

Status of RL: **machine-verified for all 65 realizable one-stub signatures
(n_B ≤ 9, |M| ≤ 2), zero violations, equality exactly at the path
signatures (s = 0, Γ_int = 0)** — the odd-cycle boundary, as it must be.
It also *predicts* non-realizability correctly: s = 0 forces Γ_int = 0,
and indeed a path with an internal M-chord plus an end-stub violates the
rooted flip condition.  RL says: *a block's interior odd-cycle mass is
controlled linearly by how far its boundary geodesic falls short of
Hamiltonian, with the additive constant supplied by the partner's minimum
distance.*  One block, three integer parameters, no potentials.

### 2.6 Verdict on task 2

* Bare leaves and crossing-free cut vertices: **theorems** (2.1, 2.2) — in
  a minimal counterexample every B-leaf is M-loaded and every articulation
  is crossed by M-edges.
* Full "minimal counterexample has 2-connected B": **open, but reduced**:
  it is *equivalent* to the pair inequality (2.5); the scalar-potential
  route is refuted (2.4); the k=1 case reduces to single-block lemma RL,
  which survives exhaustive small-case search.  Multi-stub (k ≥ 2)
  analogues of RL are the open remainder.

---

## 3. Candidate-lemma scoreboard (task 3)

Search substrate: all 18,439 valid instances with M ≠ ∅ and N ≤ 10, all
near-tight (Γ ≥ (N−1)²) instances at N = 11..13, injected C₅[3], C₅[4],
C₇[2] (`candidates.py`); the L¹ and Hölder checks were additionally run
inside the exhaustive C scan on **all** instances N ≤ 13 (`gamma_search.c`).

| # | candidate | statement | verdict | witness / reason |
|---|-----------|-----------|---------|------------------|
| C1 | Γ itself | Γ ≤ N² | **LIVE** (49.7M instances N ≤ 13, + families) | equality catalog §4 |
| C2 | path packing (L¹) | M routable in B with edge-congestion ≤ 1 | **KILLED, n=12** | `K??E@_qi?]Ia` S=63: Σ_M(d+1) = 20 > e(G) = 18, i.e. flow volume ≥ Σd = 16 > e_B = 14.  342 violating instances at n=12, none for n ≤ 11 |
| C3 | local load (L²) | ∃ routing over shortest B-paths with vertex load Σ_{C∋x} λ_C·\|C\| ≤ N (implies Γ, since Σ_x load = Γ identically) | **KILLED, n=8** | `G?`F`w` S=15: double-broom, both M-edges' every shortest path passes the hub; forced load 5+5 = 10 > 8.  523 exact kills for n ≤ 12 (512 integer hub certificates, 11 rationalized LP-dual kills, e.g. n=12 dual y = ¼(e₈+e₉+e₁₀+e₁₁), exact bound 25/2 > 12) |
| C4 | effective resistance | Σ_M (R_eff(u,v)+1)² ≤ N² | **INSUFFICIENT** (not worth pursuing) | R_eff ≤ d_B, so it is weaker than Γ (a violation would already refute Γ); and the constant fails: in C₅[2], R_eff = 3/2 exactly, (R+1)² = 25/4 < 25 — the β ≤ N²/25 step breaks |
| C5 | convex path functionals | Σ_M φ(d+1) ≤ φ(N), φ convex | **PINNED to x²** | §3.5: blow-ups force φ(5q) ≥ q²φ(5), usefulness forces φ(N) ≤ (N²/25)φ(5); φ(x)=x² is the unique power (p ≥ 2 and p ≤ 2) |
| C6 | fixed-split rooted potential D′ | Γ_int + Σ(d_j+½)² ≤ (n−½)² | **KILLED** | K₂,₂ + double stub: 25/2 > 49/4 (§2.4) |
| C7 | parametric SOC potential family | some split closes the Minkowski composition | **KILLED as method** | 15 pair obstructions (2 exact-algebraic); composites hold with slack (§2.4) |
| C9 | Hölder product | (d_max+1)·Σ_M(d+1) ≤ N² (implies Γ) | **KILLED, n=9** | `H?AFBo]` S=31: distances {6,4}: 7·12 = 84 > 81 (Γ = 74 ≤ 81 fine).  Also n=11 (126 > 121), n=12 (154 > 144, distances {6,4,4,4}) |
| RL | rooted single-stub lemma (§2.5) | Γ_int ≤ s(2d+2+s) + 2s·p(d) | **LIVE** (all 65 one-stub signatures, n_B ≤ 9; tight iff path) | recommended, §5 |

Notes.

**3.1 C2's near-miss structure.**  On every instance with N ≤ 9 C2 is
feasible (uniform shortest-path flow passes *exactly* on 2,030 of the
2,265; the remaining 235 are LP-feasible), and its cut condition is
*identical* to the max-cut flip condition S2 — single-commodity projections
of C2 are genuinely true (§2.3), which is why it survives so long.  It
fails only when multicommodity congestion exceeds what cuts can see —
first at n = 12.  At C₅[q] the uniform flow saturates every B-edge exactly
(load ≡ 1), so C2 is tight at the extremal family.

**3.1b Violation counts from the exhaustive integer sweep.**
L¹ (C2 consequence Σ_M(d+1) ≤ e(G)): 0 violations for N ≤ 11, **342 at
N = 12**, 4,769 at N = 13.  Hölder (C9): 3 at N = 9, 0 at N = 10, 5 at
N = 11, 35 at N = 12, 49 at N = 13.  Both kills are robust, not sporadic.

**3.2 By-product worth recording.**  The C2 witness `K??E@_qi?]Ia` (n=12,
e=18, degrees 2⁴3⁴4⁴, β=4, all four M-distances = 4) has β = 2e/9 > e/5:
the C₅/Petersen extremal ratio β ≤ e/5 fails already at 12 vertices once
Δ = 4 (Bondy–Locke protects only subcubic graphs).  Γ = 100 ≤ 144 holds
comfortably — Γ does *not* factor through the (β, e) statistics.

**3.3 Exactness inventory.**  C3: 512 hub certificates (pure integers) +
11 LP-dual kills re-verified in Fractions; 267 "PASS_LP" survivals were
rationalized and re-verified exactly.  C2 kill: integer counting
(Σ_M d > e_B).  C9 kills: integer products.  C2 "PASS_LP_FLOAT" entries
(373) are float-grade feasibility only — noted, and irrelevant to any kill.

**3.4 What the kills teach.**  All quantitative kills happen at
mixed-distance or forced-hub configurations — precisely the "different even
lengths" regime of §1.6.  Both equality families satisfy every candidate
with equality; the candidates fail strictly *between* the families.  This
independently reproduces the paper's "self-tight" complaint and localizes
it.

**3.5 Why nothing weaker than quadratic can work** (C5 detail).  For
monotone φ usable for Erdős: |M|·φ(5) ≤ Σφ(d+1) ≤ φ(N) needs
φ(N)/φ(5) ≤ N²/25; truth at C_{2k+1}[q] needs q²φ(2k+1) ≤ φ((2k+1)q).
At N = 5q these pin φ(5q) = q²·φ(5) exactly — quadratic on 5ℕ, and
φ(2k+1) ≤ ((2k+1)²/25)φ(5) at odd arguments.  The invariant is forced;
improvements must be structural (terms vanishing on both equality
families), not functional.

---

## 4. Equality / stability catalog (task 4)

**Within N ≤ 13, exhaustively** (every maximum cut of every connected
triangle-free graph), equality Γ = N² occurs **only** at:

| N | graph | # max cuts (all tight) | structure of tight cuts |
|---|-------|------------------------|-------------------------|
| 5 | C₅ | 5 | one M-edge, d = 4 |
| 7 | C₇ | 7 | one M-edge, d = 6 |
| 9 | C₉ | 9 | one M-edge, d = 8 |
| 10 | C₅[2] | 15 | \|M\| = 4, all d = 4 |
| 11 | C₁₁ | 11 | one M-edge, d = 10 |
| 13 | C₁₃ | 13 | one M-edge, d = 12 |

(N = 6, 8, 12: none.)  Beyond N = 13, two infinite families are tight by
construction and exact verification: **odd cycles C_{2k+1}** and **balanced
blow-ups C_{2k+1}[q]** (checked exactly for C₅[3], C₅[4], C₇[2]);
unbalanced blow-ups are strictly below (§1.4).  Note C₅[2]'s 15 tight cuts
strictly exceed its 5 blow-up rotations: even at a blow-up, non-blow-up
maximum cuts exist and are *also* tight — equality is a property of the
whole max-cut set there.

**Uniqueness verdict:** the balanced C₅ blow-up is **not** the unique
tight configuration.  The correct equality set (exhaustive in range,
conjecturally in general) is

    { C_{2k+1}[q] : k ≥ 2, q ≥ 1 }   (odd cycles = the q = 1 members),

with no sporadic cases for N ≤ 13.

**Consequences for strengthenings** (what the catalog is for):

1. Any correct strengthening must vanish on odd cycles *and* balanced
   blow-ups simultaneously.  The families sit at opposite ends of the
   distance spectrum (one M-edge at d = N−1 vs. q² M-edges at constant
   small d) — exactly why the L¹-, L∞- and product-type sharpenings all
   die: each is tight on both families but bulges on mixtures (§3.4).
2. The near-tight non-equal instances are *glued odd cycles* at cut
   vertices for 6 ≤ N ≤ 12: max Γ below N² is 25 (N=6,7: C₅+pendant),
   50 = 25+25 (N=8), 74 = 49+25 (N=9), 81 (N=10: C₉+pendant),
   106 = 81+25 (N=11), 130 = 81+49 (N=12); at N=13 the maximum 150 = 6·25
   is blow-up-like (6 M-edges, all d = 4, e = 30).  Stability at cut
   vertices ("tight + articulation ⟹ odd cycle") holds exhaustively in
   range.
3. A usable stability form dictated by the data: Γ ≤ N² − (defect terms
   vanishing exactly on the C_{2k+1}[q] family), the defect visible in the
   boundary slack s of §2.5.  RL is the k=1 quantification of exactly
   this.

---

## 5. Recommendation: the ONE lemma to attempt properly

**Attempt Lemma RL (§2.5), then its multi-stub analogue.**

    RL:  for every valid rooted instance (B, M, w, σ) with a single stub
         at distance d from w, and s = n − 1 − d:
             Γ_int  ≤  s·(2d + 2 + s) + 2·s·p(d).

Reasons, in order of weight:

1. **It closes a real gap.**  RL ⟹ the k=1 pair inequality ⟹ (with
   theorems 2.1/2.2) no minimal counterexample has a cut vertex crossed by
   exactly one M-edge.  Together with the crossing-free case this is most
   of the block-decomposition reduction — and by §2.3 the reduction is
   *exactly equivalent* to the cut-vertex case of Γ, not merely
   sufficient.
2. **Single-block statement, three integers of boundary data** (n, d,
   Γ_int).  It survived the graveyard precisely because it does *not*
   aggregate across blocks — the provably fatal move (§2.4).
3. **Exhaustive machine support in range**: all realizable one-stub
   signatures to n_B = 9, equality exactly at the path/odd-cycle boundary
   — the right tightness structure, unlike every killed candidate.
4. **Proof surface exists.**  The rooted flip condition is a
   single-commodity cut condition; by Gale–Hoffman the stub routes to w
   edge-disjointly from the M-structure (§2.3), and s measures the
   non-Hamiltonicity of the stub geodesic — the two ingredients the RHS is
   built from.  Plausible attack: induct along the stub geodesic, charging
   interior M-edges to the ≥ s off-geodesic vertices via S2 with
   T = geodesic prefixes (the flip family that already proves the rigidity
   s = 0 ⟹ Γ_int = 0).
5. **The known-open core is quarantined.**  RL says nothing about
   2-connected B (the paper's self-tight core), so attempting it does not
   secretly require the conjecture — unlike C3/C9, which implied Γ
   outright and were therefore doomed to be self-tight or false.

Fallback if RL resists: prove RL restricted to Γ_int coming from a single
internal M-edge (the two-parameter mixed family {d_int, d_stub} — every
small D′/SOC obstruction lives there).

---

## 6. Scripts, logs, exactness (appendix)

All in `compute23/gate2/`; single-threaded, `nice -19`.

| file | role | runtime |
|---|---|---|
| `common.py` | exact utilities: graph6, brute max cut, instance extraction + side-condition asserts, blow-ups, flip checker, shortest-path counts | — |
| `verify_c5_blowup.py` → `logs_verify_c5.txt` | task-1 sanity: blow-up equalities, odd cycles, unbalanced strictness, flip characterisation — ALL PASS | 25 s |
| `gamma_search.c` (+ binary) | exhaustive N ≤ 13 sweep: Γ, asserts S3/S4/S5/S7′, equality catalog, near-tight dump, integer L¹ (C2) and Hölder (C9) checks | n ≤ 12: ~12 s; n = 13: ~3.5 min ×2 |
| `logs_search_n5_9.txt`, `logs_search_n10/11/12.txt`, `logs_search_n13.txt` | first sweep: per-n Γ/EQ/CEX results (§1.5) | — |
| `logs_search_l1c9_n5_12.txt`, `logs_search_n13_l1c9.txt` | second sweep with integer L¹/Hölder checks; Γ/EQ/CEX identical to first sweep (§3.1b counts) | — |
| `dump_n5..13.txt` | instance dumps (graph6 + colour mask): all M≠∅ for N ≤ 10, near-tight for 11–13 | — |
| `candidates.py` → `logs_candidates.txt`, `candidate_kills.txt` | C2/C3 testing: exact uniform routing, integer hub certificates, LP (float) with exact rational re-verification of every verdict used | ~4 min |
| `rooted_search.py` → `logs_rooted.txt` | rooted enumeration n_B ≤ 9 (478,000 valid instances, 165 signatures), D′ test, SOC pairing, TRUE pair inequality (stage B′), composite assembly + brute-force validation (stage C) | 15 s |

Exactness rules honoured: every KILL and every equality/inequality claim
in this document is integer/Fraction arithmetic end-to-end; scipy/HiGHS
floats only *proposed* certificates, which were then rationalized and
re-verified exactly (or replaced by integer hub/counting certificates).
The second n=13 sweep re-ran the full enumeration with the integer L¹ and
Hölder checks added; its Γ/EQ/CEX numbers match the first run bit-for-bit
(n=13: EQ=13, CEX=0, same MAXNONEQ witness; L1VIOL=4,769, C9VIOL=49 —
recorded in `logs_search_n13_l1c9.txt`).

Hard stops respected: no LP/flag-order work on the paper's certificate; no
attempt at the 2-connected core; ≤ 2 cores throughout; no files outside
`compute23/gate2/` touched.
