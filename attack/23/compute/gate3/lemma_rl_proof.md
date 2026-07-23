# Gate 3 — Lemma RL (Erdős #23): a complete proof attempt

Scope: prove Lemma RL of `compute23/gate2/analysis.md` §2.5 by hand, with
every step written out and machine-verified.  All computation in this gate
is exact integer arithmetic, ≤ 2 cores, `nice -19`, confined to
`compute23/gate3/` (scripts and logs inventoried in §12).

**Honesty convention.**  Every numbered claim carries one of three labels:

* **PROVED** — a complete hand proof is written out below, and the claim is
  additionally machine-verified on the exhaustive small-case data.
* **VERIFIED-BUT-UNPROVED** — machine-verified exhaustively in the stated
  range (plus targeted and random families beyond it), no hand proof.
* **GAP** — the precise open sub-statement; nothing below hides inside it.

---

## 0. Executive summary

1. **Difficulty calibration (new, PROVED, §2.4).**  Lemma RL *as stated* —
   universally quantified over all valid one-stub rooted instances — is
   **not an easier statement than Conjecture Γ**: it is sandwiched
   Γ ⟹ RL ⟹ (Γ up to an additive `8n − 9`).  The lower sandwich comes
   from a two-line pendant-stub construction (Theorem 2.7).  Any complete
   elementary proof of RL would prove the paper's obstruction up to O(N),
   i.e. β ≤ N²/25 + O(N) for Erdős #23.  A "complete proof of RL by hand"
   therefore cannot be expected from elementary arguments alone; the gate-2
   memo's target should be re-aimed at the *inductive form* RL\*
   (§7), which suffices for the corollary chain and is genuinely weaker.
2. **What is fully proved here.**
   * The flow/cut reformulation of rooted validity, the Gale–Hoffman
     single-commodity content, and the exact equivalence
     *RL ⟺ Conjecture Γ on the minimal path-partner composite* (§2).
   * All reductions: M-free leaf deletion, M-loaded leaf deletion, root
     move, stub retraction (§3.1–3.4).
   * Rigidity: s = 0 ⟹ M = ∅, and s = 1 ⟹ M = ∅ (§3.5–3.6).
   * RL for **trees** (any |M|), with slack (§3.7).
   * The **charging lemma** (each off-corridor vertex absorbs at most two
     forced level-crossings, §4.4) — the engine of the single-edge laws.
   * The single-edge laws **SE1 (D ≤ 2s)** and **SE2 (2D ≤ 2s + d)**
     for every valid one-stub instance with `|M|=1`.  The formerly open
     off-corridor case is closed by the symmetric component-ledger theorem
     (§5.3; complete proof and hostile audit in
     `gap_ga_component_ledger.md` and `gap_ga_audit.md`).
   * **RL for |M| = 1** outright: component ledger gives SE1 and SE2, and
     their algebraic implication has ample slack (§6).
   * The **large-slack theorem**: RL holds whenever 2·s·p(d) ≥ (d+1)²,
     *given* Conjecture Γ on ≤ n vertices; unconditionally for n ≤ 13
     via gate 2's exhaustive verification (§7).
   * The full corollary chain from RL (or RL\*) to "no (minimal)
     counterexample has a cut vertex crossed by exactly one M-edge" (§9).
3. **What remains (the honest gap, §8).**
   * **G-A is PROVED.**  The component-span ledger closes every
     off-corridor single-edge configuration; its first hostile audit found
     a false intermediate subclaim, and the repaired bound passed a second
     node-by-node audit plus 390,022 general two-demand checks.
   * **G-B** remains: the multi-edge aggregation of the charging argument in the
     middle regime 2 ≤ s < (d+1)²/(2p(d)).  By Theorem 2.7 the
     unconditional form of this gap *contains the conjecture's hard
     quadratic content*; for small s it is strongly rigid (max Γ observed
     at s = 2 is 25, flat in d).
4. **Verification totals.**  Zero violations of RL, SE1, SE2 across
   ~162M exhaustive valid one-stub rooted instances: all 17.5M with
   n ≤ 11, |M| ≤ 2 (65 signatures at n ≤ 9 — bit-for-bit the gate-2
   catalogue); all with n ≤ 9 and unbounded |M|; all 144.3M with n ≤ 12,
   |M| = 1; exhaustive thin-corridor families (s = 2, d ≤ 13; s = 3,
   d ≤ 11); ~1.1M random rooted instances at 12 ≤ n ≤ 16.  Every proof
   step below is separately machine-checked (§12).  The new G-A harness
   additionally checked 29,050 geodesic pairs and 36,112 off-corridor
   components, including 10,636 exceptional components.

---

## 1. The statement, self-contained

All graphs are finite and simple.

**Definition 1.1 (rooted instance, gate 2 §2.3).**  A *rooted instance*
R = (B, M, w, σ) consists of

* a connected bipartite graph B on n vertices (the *cut graph*),
* a set M of *internal edges*: unordered pairs uv of distinct vertices on
  the same side of B's bipartition with d_B(u,v) ≥ 4 (same-side forces
  d_B(u,v) even), such that B ∪ M is simple and triangle-free,
* a marked vertex w (the *root*; the articulation being cut),
* stub counts σ : V∖{w} → ℕ (σ(u) = number of crossing M-edges cut at w
  whose near endpoint is u),

subject to the **rooted flip condition**

    (RFC)   ∀ T ⊆ V∖{w} :   e_M(δT) + σ(T)  ≤  e_B(δT),

where δT is the set of edges with exactly one endpoint in T, e_M/e_B count
M/B-edges in δT, and σ(T) = Σ_{u∈T} σ(u).

**Definition 1.2 (one-stub instance).**  R is *one-stub* if σ is the
indicator of a single vertex x₀ ≠ w.  Write

* d := d_B(w, x₀) ≥ 1  (the stub distance),
* s := n − 1 − d ≥ 0  (the *slack*: vertices beyond a w–x₀ geodesic),
* Γ_int := Σ_{uv∈M} (d_B(u,v) + 1)²  (the internal Γ-mass),
* D_uv := d_B(u, v) for uv ∈ M; when |M| = 1, D denotes its distance.

**Definition 1.3 (parity-minimal partner distance).**
p(1) = 3, p(2) = 2, p(3) = 1, p(d) = 2 for even d ≥ 4, p(d) = 1 for odd
d ≥ 5.  Equivalently: p(d) is the least δ ≥ 1 with d + δ even and ≥ 4.
Note 1 ≤ p(d) ≤ 3 and d + p(d) is always even and ≥ 4.

**Lemma RL (the target).**  *For every valid one-stub rooted instance,*

    Γ_int  ≤  s·(2d + 2 + s) + 2·s·p(d).

**Remark 1.4 (equivalent right-hand sides; machine-checked C3).**  With
n = d + 1 + s and p = p(d),

    s(2d+2+s) + 2sp  =  n² − (d+1)² + 2sp  =  s·(s + 2(d + p + 1)).

So RL says: *the interior odd-cycle mass may exceed n² − (d+1)² only by
the correction 2sp; equivalently each off-geodesic vertex carries at most
s + 2(d+p+1) of Γ-mass.*  For s = 0 the bound is 0.

Background (gate 2): Conjecture Γ states that every *valid instance* —
a triangle-free graph G with a maximum cut χ, M its monochromatic edges,
B its (connected, spanning) cut graph — satisfies
Γ := Σ_{uv∈M} (d_B(u,v)+1)² ≤ N² on N vertices.  Γ implies Erdős #23
(β(G) ≤ N²/25).  Validity of (G,χ) is characterized by the flip condition
(S2): ∀ T ⊆ V: e_M(δT) ≤ e_B(δT).  Γ is verified exhaustively for
N ≤ 13 (gate 2 §1.5, 49.7M max-cut instances).

---

## 2. Foundations: the flow reformulation and the two-sided sandwich

### 2.1 Symmetric form of the rooted flip condition

**Lemma 2.1 (PROVED; machine check C2, 4,622 comparisons).**  A one-stub
tuple (B, M, w, x₀) satisfies RFC iff

    (RFC†)   ∀ T ⊆ V :   e_M(δT) + [T separates w from x₀]  ≤  e_B(δT),

where [·] is 1 if exactly one of w, x₀ lies in T.

*Proof.*  δT = δ(V∖T), so e_M and e_B are invariant under complementation,
and so is the separation indicator.  Given T, exactly one of T, V∖T avoids
w; call it T′.  If T separates w, x₀ then x₀ ∈ T′, so σ(T′) = 1 equals the
indicator; if not, x₀ ∉ T′ and σ(T′) = 0 equals it.  Thus each RFC†
constraint is an RFC constraint for T′ and conversely (T ⊆ V∖{w} has
T′ = T).  ∎

RFC† says exactly: **the demand multigraph H = M ∪ {w x₀} satisfies the
multicommodity cut condition in B with unit capacities.**  Two immediate
consequences:

**Lemma 2.2 (PROVED).**  (i) Dropping the stub, (B, M) satisfies the
unrooted flip condition S2; hence (B ∪ M, χ_B) is a valid instance on n
vertices (B is connected and spanning by hypothesis, B ∪ M triangle-free
by hypothesis).  (ii) RFC is monotone: removing M-edges or stubs preserves
validity; adding B-edges (keeping B ∪ M triangle-free, bipartite) preserves
validity.

*Proof.*  (i) RFC† with the separation term discarded.  (ii) Each
constraint's LHS decreases / RHS increases.  ∎

### 2.2 Gale–Hoffman: the single-commodity content

**Proposition 2.3 (PROVED).**  Let B be connected bipartite, w a vertex,
σ : V∖{w} → ℕ, and M = ∅.  Then (B, ∅, w, σ) is rooted-valid iff σ can be
routed to w integrally with unit edge capacities: there exist
Σ_u σ(u) paths, σ(u) of them from u to w, pairwise edge-disjoint.

*Proof.*  Add an apex t joined to each u by σ(u) parallel edges; RFC says
every cut separating t-side from w has B-capacity ≥ demand; by max-flow
min-cut (integral version) the flow exists; conversely edge-disjoint paths
witness every cut inequality.  ∎

This is gate 2's structural corollary (§2.3 there): crossing M-edges at an
articulation extend to edge-disjoint B-paths into w.  For one stub it
degenerates to connectivity; its real use is the multi-stub setting (§11).
With M ≠ ∅ the cut condition is genuinely multicommodity and feasibility
may fail (gate 2's C2 kill at n = 12) — RFC is the *cut condition itself*,
and everything below uses only that.

### 2.3 The minimal-composite equivalence

**Definition 2.4.**  Given a one-stub R with data (n, d, Γ_int), the
*minimal composite* Ĝ is built by attaching a pendant path
w = y₀ − y₁ − ⋯ − y_p (p = p(d), new vertices) to B, and adding the
crossing edge e* = x₀ y_p to M.  Set B̂ = B + path, M̂ = M ∪ {e*},
N = n + p, χ̂ = the 2-colouring of B̂ (proper on B̂; well-defined since B̂
is connected bipartite).

**Proposition 2.5 (PROVED; machine check C1 on all 65 signature
witnesses).**  Ĝ = B̂ ∪ M̂ is a valid instance on N vertices:
B̂ ∪ M̂ is simple and triangle-free, χ̂ is a maximum cut with cut graph
B̂ connected spanning, and

    Γ(Ĝ) = Γ_int + (d + p + 1)²,     d_{B̂}(x₀, y_p) = d + p.

Consequently **RL for R  ⟺  Γ(Ĝ) ≤ N²**, because
N² − (d+p+1)² = s(2d+2+s) + 2sp   (Remark 1.4 with N = n + p).

*Proof.*  *Distances.*  Every path from y_p into B passes y_{p−1}, …, y₁,
w, so d_{B̂}(y_p, z) = p + d_B(w, z) for z ∈ B; in particular
d_{B̂}(x₀,y_p) = d + p, which is even and ≥ 4 by Definition 1.3, so e* is
a legal M-edge; distances inside B are unchanged (the pendant path creates
no shortcuts).  *Simplicity/triangles.*  y_p is new, so e* is not a
doubled edge.  A triangle through e* needs a common neighbour of x₀ and
y_p in B̂ ∪ M̂; the only candidate is y_{p−1}.  If p ≥ 2, y_{p−1} is an
interior tail vertex whose only B̂ ∪ M̂-neighbours are y_{p−2}, y_p.  If
p = 1, y_{p−1} = w; but p(d) = 1 forces d odd ≥ 3, so w x₀ ∉ B (that
would mean d = 1) and w x₀ ∉ M (M-distances are even, d is odd).  So
no new triangle; B ∪ M was triangle-free.  *Maximality (S2 for Ĝ).*  Let
T ⊆ V(Ĝ); we verify e_{M̂}(δT) ≤ e_{B̂}(δT).  Write T_B = T ∩ V(B) and let
j ∈ {0,…,p} count the tail edges of δT (edges y_i y_{i+1} with exactly one
endpoint in T, y₀ = w).  Then e_{B̂}(δT) = e_B(δT_B) + j and
e_{M̂}(δT) = e_M(δT_B) + [e* ∈ δT].  If j ≥ 1: by S2 for (B, M)
(Lemma 2.2(i)) and [e* ∈ δT] ≤ 1,
e_{M̂}(δT) ≤ e_B(δT_B) + 1 ≤ e_B(δT_B) + j = e_{B̂}(δT).
If j = 0, the tail lies entirely
on one side of T; then y_p and w are on the same side, so e* ∈ δT iff T
separates x₀ from y_p iff T separates x₀ from w, i.e.
[e* ∈ δT] = [T_B separates w, x₀]; RFC† at T_B gives exactly
e_{M̂}(δT) ≤ e_B(δT_B) = e_{B̂}(δT).  So χ̂ is a maximum cut (S2 is the
complete characterisation, gate 2 §1.2), with cut graph B̂ (connected,
spanning).  *Γ identity.*  M̂-distances: unchanged for M; d + p for e*.  ∎

**Converse (Γ ⟹ RL, PROVED).**  If Conjecture Γ holds on N = n + p
vertices then Γ(Ĝ) ≤ N², i.e. RL holds for R.  So **RL is exactly the
restriction of Conjecture Γ to minimal composites** — instances whose cut
graph has a pendant path of length p(d) whose tip carries the only M-edge
touching the path.

### 2.4 The sandwich: RL is conjecture-hard

**Theorem 2.6 (pendant-stub construction; PROVED; machine check
S-pendant, 629 + exhaustive-in-range cases).**  Let (G, χ) be *any* valid
unrooted instance on n₁ vertices with cut graph B₁ and monochromatic set
M₁, and let w ∈ V(G) be arbitrary.  Attach a new pendant vertex x₀ to w
(a B-edge).  Then (B₁ + wx₀, M₁, w, x₀) is a valid one-stub rooted
instance with d = 1, s = n₁ − 1.

*Proof.*  Let T ⊆ (V₁ ∪ {x₀})∖{w}.  If x₀ ∉ T: δT in the new graph equals
δT in B₁ plus possibly wx₀ — but w, x₀ ∉ T so wx₀ ∉ δT; RFC's LHS is
e_{M₁}(δT) + 0 ≤ e_{B₁}(δT) by S2.  If x₀ ∈ T: T = T₁ ∪ {x₀};
x₀ has the single edge wx₀, and w ∉ T, so e_B(δT) = e_{B₁}(δT₁) + 1,
while e_M(δT) + σ(T) = e_{M₁}(δT₁) + 1 ≤ e_{B₁}(δT₁) + 1 by S2.  ∎

**Theorem 2.7 (difficulty calibration; PROVED).**

    Conjecture Γ   ⟹   Lemma RL   ⟹   Γ up to O(N):
    RL restricted to its d = 1 slice already implies that EVERY valid
    unrooted instance on n₁ vertices has Γ ≤ n₁² + 8n₁ − 9.

*Proof.*  Left arrow: Proposition 2.5.  Right arrow: apply Theorem 2.6 to
(G, χ) at any w; RL for the resulting instance (n = n₁ + 1, d = 1,
s = n₁ − 1, p(1) = 3) gives
Γ(G) = Γ_int ≤ s(2d+2+s) + 2sp = s(s+4) + 6s = s(s+10)
     = (n₁−1)(n₁+9) = n₁² + 8n₁ − 9.  ∎

**Consequence.**  RL as a standalone universally-quantified lemma carries
the conjecture's full quadratic content.  Its "hard direction" is *not*
the thin-corridor regime (small s — strongly rigid, see §5) but the
d = O(1), s = Θ(n) regime, where RL is Γ-with-linear-slack for arbitrary
valid instances.  This redirects the attack (as anticipated by the gate-2
memo's use of RL *inside a minimal-counterexample induction*): the
operative target is

**RL\* (inductive form).**  *If Conjecture Γ holds for all valid instances
on ≤ n vertices, then every valid one-stub rooted instance on n vertices
satisfies RL.*

RL\* suffices for the one-stub (`k=1`) block corollary in §9, because in a
minimal counterexample of size N every proper block has n ≤ N − 1. It does
not supply the multi-stub inequality explicitly left open in §11, nor the
final connected/2-connected case. Section 7 proves RL\* on a large explicit
regime; §§4–6 attack the remaining one-stub regime unconditionally.

---

## 3. Reductions and rigidity (all PROVED)

Throughout, R = (B, M, w, x₀) is a valid one-stub rooted instance and
"valid" always means RFC.  Machine checks: S-leafdel, S-mleafdel,
S-rootmove, S-stubmove, S-s01, S-tree in `rl_steps.py` (exhaustive
n ≤ 9, |M| ≤ 2; zero failures).

**Lemma 3.1 (M-free leaf deletion).**  Let z be a leaf of B with
z ∉ {w, x₀} and z not an endpoint of any M-edge.  Then
(B − z, M, w, x₀) is valid, with the same d, the same M-distances
(hence Γ_int), and s decreased by 1.  Moreover the RL right-hand side
strictly decreases, so a counterexample stays a counterexample.

*Proof.*  Let y be z's unique neighbour.  Take T ⊆ (V∖{z})∖{w}.  If
y ∉ T then δT is unchanged by deleting z, and RFC(T) in B gives the
claim.  If y ∈ T, apply RFC in B to T ∪ {z}: since z's only edge is zy
with both endpoints now in T ∪ {z}, e_B(δ(T∪{z})) = e_B(δT) − 1 =
e_{B−z}(δT); and e_M, σ are unchanged (z carries neither).  Distances
between remaining vertices never route through a leaf.  RHS decreases by
(2s + 2d + 2p + 1) > 0 (Remark 1.4 differentiated in s).  ∎

**Lemma 3.2 (root move).**  If w is a leaf with neighbour w′, d ≥ 2, and
w is not an M-endpoint, then (B − w, M, w′, x₀) is valid with stub
distance d − 1, the same Γ_int and s.  The RL right-hand side does not
increase (checking all parity cases of p): the change is
s·(−2 + 2(p(d−1) − p(d))) ≤ 0 since p(d−1) ≤ p(d) + 1 always.

*Proof.*  New constraints are over T ⊆ (V∖{w})∖{w′}.  Such T contains
neither w nor w′, so the edge ww′ ∉ δT and z := w has no other edges:
δT is unchanged by deleting w; RFC(T) in B (T avoids w) gives the
constraint, with σ unchanged.  d_B−w(w′, x₀) = d − 1 because a w–x₀
geodesic starts with ww′ (w is a leaf).  For the p-cases:
(p(d−1) − p(d)) ∈ {−1, 0, +1} and equals +1 only when the −2 absorbs it. ∎

**Lemma 3.3 (stub retraction).**  If x₀ is a leaf with neighbour x′,
d ≥ 2, and x₀ is not an M-endpoint, then (B − x₀, M, w, x′) is valid with
stub distance d − 1, same Γ_int and s; the RL right-hand side does not
increase (same p-case check as 3.2).

*Proof.*  Constraints for the new instance: T ⊆ (V∖{x₀})∖{w}, demand
[x′ ∈ T].  If x′ ∉ T: δT unchanged (x₀, x′ ∉ T), and old RFC(T) has
σ-term 0 = new term.  If x′ ∈ T: apply old RFC to T ∪ {x₀}:
e_B(δ(T∪{x₀})) = e_B(δT) − 1 = e_{B−x₀}(δT) (edge x₀x′ becomes internal;
x₀ has no other edges), e_M unchanged (x₀ ∉ V(M)), and σ(T∪{x₀}) = 1 =
new demand.  ∎

**Lemma 3.4 (M-loaded leaf deletion).**  Let z ∉ {w, x₀} be a leaf of B
that IS an M-endpoint, M_z its incident M-edges.  Then
(B − z, M∖M_z, w, x₀) is valid; Γ_int drops by Σ_{zv∈M_z}(d_B(z,v)+1)²;
s drops by 1.

*Proof.*  Let y = z's B-neighbour, T ⊆ (V∖{z})∖{w}.  If y ∉ T:
e_{B−z}(δT) = e_B(δT) and e_{M∖M_z}(δT) ≤ e_M(δT); old RFC(T) applies.
If y ∈ T: old RFC at T ∪ {z} reads
e_M(δT) − c + c′ + σ(T) ≤ e_B(δT) − 1, where c = #{zv ∈ M_z : v ∈ T} and
c′ = #{zv ∈ M_z : v ∉ T} ≥ 0 are the M_z-crossings before/after moving z
in.  Hence e_{M∖M_z}(δT) + σ(T) = e_M(δT) − c + σ(T) ≤ e_B(δT) − 1 − c′
≤ e_{B−z}(δT).  ∎

**Theorem 3.5 (s = 0 rigidity).**  s = 0 forces B = the w–x₀ path P_d and
M = ∅; RL holds with equality 0 = 0.

*Proof.*  All n = d + 1 vertices lie on a w–x₀ geodesic
u₀u₁⋯u_d, so B ⊇ this path; an extra edge u_iu_j (|i−j| ≥ 2) would give
d_B(u_i,u_j) = 1 < |i − j|, contradicting geodesy.  If u_au_b ∈ M
(b − a ≥ 4), take T = {u_b, …, u_d}: e_B(δT) = 1 (only u_{b−1}u_b),
e_M(δT) ≥ 1 (u_au_b crosses), σ(T) = 1 (x₀ = u_d ∈ T): 2 > 1 violates
RFC.  ∎

**Theorem 3.6 (s = 1 rigidity).**  s = 1 forces M = ∅.

*Proof.*  Fix a w–x₀ geodesic P: w = u₀, …, u_d = x₀, and let f be the
unique off-geodesic vertex.  Any two P-neighbours u_i, u_j of f satisfy
|i − j| = d_B(u_i,u_j) ≤ 2 and |i−j| even ≠ 0, so f's P-neighbourhood is
{u_{c−1}, u_{c+1}} or a single u_{c₀}; f has no other possible
neighbours.  M-edges have three shapes.

*(i) Both endpoints on P*: u_au_b with b − a = D ≥ 4 (f cannot shorten a
P-distance: the detour u_{c−1} f u_{c+1} has length 2 = the P-distance).
Consider suffix sets S_k := {u_k, …, u_d} for 1 ≤ k ≤ d.  RFC at
T = S_k: e_B(δS_k) = 1 + e(f, S_k) (the corridor edge u_{k−1}u_k plus
f's edges into the suffix; f ∉ S_k), e_M(δS_k) = [a < k ≤ b], σ = 1;
so for k ∈ (a, b]: e(f, S_k) ≥ 1, i.e. f has an anchor at position ≥ k.
RFC at T = S_k ∪ {f}: e_B = 1 + e(f, P_{<k}), e_M = [a < k ≤ b] (both
endpoints on P, unaffected by f), σ = 1; so for k ∈ (a, b]: f has an
anchor at position < k.  With anchors confined to {c−1, c+1}
(Lemma 4.2) this forces c + 1 ≥ k and c − 1 < k, i.e. k ∈ {c, c+1},
for every k ∈ (a, b].  So D = b − a ≤ 2 < 4, contradiction.

*(ii) Endpoint f*: M-edge f u_b.  Sub-case f has one P-neighbour u_{c₀}
(f a leaf): D = d_B(f, u_b) = 1 + |c₀ − b| ≥ 4.  RFC at S_k:
e_B = 1 + [c₀ ≥ k], e_M = [b ≥ k] (f ∉ S_k, so the M-edge crosses iff
u_b ∈ S_k), σ = 1: hence [b ≥ k] ≤ [c₀ ≥ k] for all k, so b ≤ c₀.
RFC at S_k ∪ {f}: e_B = 1 + [c₀ < k], e_M = [b < k], σ = 1: hence
b ≥ c₀.  So b = c₀ and D = 1 < 4, contradiction.  Sub-case f has two
P-neighbours u_{c−1}, u_{c+1}: D = d_B(f, u_b) = 1 + min(|c−1−b|,
|c+1−b|).  RFC at S_k gives [b ≥ k] ≤ [c+1 ≥ k] (f's suffix-edges:
2 if k ≤ c−1, 1 if k ∈ {c, c+1}, 0 if k ≥ c+2), i.e. b ≤ c + 1; RFC at
S_k ∪ {f} gives (e_B = 1 + #{f-P-edges to prefix} = 1 + [c−1 < k] +
[c+1 < k]) the constraint [b < k] ≤ [c − 1 < k], i.e. b ≥ c − 1.  So
|b − c| ≤ 1 and D ≤ 1 + 2 = 3 < 4, contradiction.

*(iii) Both endpoints off P*: impossible, |F| = 1.  ∎

**Theorem 3.7 (trees; any |M|).**  If B is a tree, then
Σ_{uv∈M} d_B(u,v) + d ≤ n − 1, and RL holds with slack:
Γ_int ≤ (s+1)² ≤ s(2d+2+s) + 2s·p(d).

*Proof.*  For a tree edge e, let C_e be the component of B − e not
containing w, and T = C_e: e_B(δT) = 1, so RFC gives: (# M-edges whose
endpoints are separated by e) + [x₀ ∈ C_e] ≤ 1.  A demand's unique tree
path uses e iff e separates its endpoints; summing over all n − 1 edges,
Σ_M d_B(u,v) + d ≤ n − 1.  Hence Σ_M (D_uv + 1) ≤ (n − 1 − d) + |M| =
s + |M|, with every term ≥ 5, so |M| ≤ s/4.  Maximising Σ x_i² over
x_i ≥ 5, Σ x_i ≤ s + m, m = |M| fixed: the maximum is
(s − 4m + 5)² + 25(m − 1), which is decreasing in m for m ≤ s/4 (the
increment is −8s + 32m − 31 < 0); so Γ_int ≤ (s + 1)² (m = 1; m = 0 is
trivial).  Finally s(s + 2d + 2 + 2p) − (s+1)² = 2s(d + p) − 1 ≥
2s·2 − 1 > 0 for s ≥ 1; and s = 0 is Theorem 3.5.  ∎

**Corollary 3.8 (minimal counterexample structure).**  A counterexample
to RL minimising n has: every B-leaf in {w, x₀} ∪ V(M); if w (resp. x₀)
is a leaf then d = 1 or w ∈ V(M) (resp. x₀ ∈ V(M)); B is not a tree;
s ≥ 2; and, by the exhaustive verification (§12), n ≥ 10, with |M| ≥ 3
if n ≤ 11 and |M| ≥ 2 if n = 12.  (PROVED, from 3.1–3.7 + machine data.)

---

## 4. The corridor framework

Fix a valid one-stub R and a w–x₀ geodesic P: w = u₀, u₁, …, u_d = x₀
(the *corridor*).  Let F := V ∖ P, s = |F|.  Let a(z) := d_B(w, z)
(*levels*); a(u_j) = j.

**Lemma 4.1 (levels; PROVED).**  In connected bipartite B every edge
joins consecutive levels: |a(x) − a(y)| = 1 for xy ∈ E(B).  Hence
Σ_{r≥1} b_r = e(B), where b_r := #edges between levels r−1 and r.
Moreover the only corridor vertices at levels r−1, r are u_{r−1}, u_r
(for r ≤ d), so **every edge between levels r−1 and r other than the
corridor edge u_{r−1}u_r has an endpoint in F at level r−1 or r**.

*Proof.*  BFS levels differ by ≤ 1 across an edge always; equality of
levels across an edge closes an odd walk through w, impossible in
bipartite.  Corridor positions equal levels because P is a geodesic from
w.  Two corridor vertices at consecutive levels r−1, r are u_{r−1}, u_r
and the unique B-edge between them is the corridor edge (simplicity).  ∎

**Lemma 4.2 (attachment; PROVED; machine check S-attach).**  Every f ∈ F
has at most two neighbours on P, located at positions {c−1, c+1} for
some c (or a single position).

*Proof.*  P-neighbours u_i, u_j of f satisfy d_B(u_i,u_j) ≤ 2, i.e.
|i − j| ≤ 2, and bipartiteness forces |i − j| even; ≠ 0 by simplicity. ∎

**Lemma 4.3 (canonical level cuts; PROVED).**  For 1 ≤ r ≤ d the level
cut Λ_r := {z : a(z) ≥ r} satisfies: w ∉ Λ_r, x₀ ∈ Λ_r, and RFC gives

    e_M(δΛ_r) + 1 ≤ e_B(δΛ_r) = b_r.

An M-edge yz *crosses level r* iff min(a(y),a(z)) < r ≤ max(a(y),a(z));
crossing is canonical (no subset freedom).

*Proof.*  a(x₀) = d ≥ r > 0 = a(w); δΛ_r is exactly the level-(r−1,r)
edge set by Lemma 4.1.  ∎

**Lemma 4.4 (THE CHARGING LEMMA; PROVED; machine check G1).**  Let
W ⊆ [1, d] be a set of levels such that for every r ∈ W at least one
M-edge crosses level r (any |M|).  Then

    |W| ≤ 2·#{f ∈ F : a(f) ∈ [min W − 1, max W]} ≤ 2s.

*Proof.*  Fix r ∈ W.  By Lemma 4.3, b_r ≥ e_M(δΛ_r) + 1 ≥ 2, so besides
the corridor edge there is an edge between levels r−1 and r; by Lemma 4.1
it has an endpoint f_r ∈ F with a(f_r) ∈ {r−1, r}.  Charge r to f_r.  A
fixed f ∈ F can be charged only by r ∈ {a(f), a(f)+1}: at most twice.
The charged vertices have levels in [min W − 1, max W].  ∎

*(Scope: the lemma counts **levels**, with multiple simultaneous
crossings absorbed by a single charge.  What fails for |M| ≥ 2 is the
aggregated form Σ_{uv∈M} |W_uv| ≤ 2s with multiplicity: distinct crossing
edges at the same level may share their F-endpoint, and RL for |M| ≥ 2
needs a multiplicity-weighted count.  This is exactly gap G-B; see §8.)*

**Lemma 4.5 (bridges; PROVED; machine check MSL).**  Let e be any bridge
of B whose removal separates w from x₀ (in particular any corridor edge
u_{k−1}u_k that is a bridge).  Then no M-edge joins the two components of
B − e; hence no M-geodesic ever uses such a bridge.

*Proof.*  Let T = the component of B − e not containing w.  Then
e_B(δT) = 1 and T separates w from x₀ (x₀ ∈ T since e disconnects them
— for a corridor bridge, x₀'s side is the suffix side).  RFC†:
e_M(δT) + 1 ≤ 1 forces e_M(δT) = 0.  A simple path crosses a bridge iff
its endpoints are separated by it.  ∎

**Proposition 4.6 (wall networks; PROVED; for completeness).**  For
k ∈ [1, d] let N_k be the graph obtained from B by deleting the corridor
edge e_k = u_{k−1}u_k and contracting the corridor suffix
S_k = {u_k,…,u_d} to a node σ* and the prefix to τ*.  RFC restricted to
the family {S_k ∪ A : A ⊆ F} says precisely: for every k, the demands
{(σ*, τ*)} ∪ M (mapped into N_k) satisfy the multicommodity cut condition
in N_k + e_k.  In particular (component form): if some union of
N_k-components contains σ* and not τ*, it separates no M-edge.

*Proof.*  e_B(δ(S_k∪A)) = 1 + β_k(A) where β_k(A) := e(F∖A, S_k) +
e(A, P_{<k}) + e(A, F∖A) enumerates the N_k-cut with sink side
τ* ∪ (F∖A); the +1 is e_k; σ(S_k∪A) = 1 always (x₀ = u_d ∈ S_k, w ∉).
Zero-capacity cuts β_k(A) = 0 are exactly unions of N_k-components
containing σ*'s and omitting τ*'s, giving the component form.  ∎

---

## 5. The single-edge laws

**Definition/Statement.**  For a valid one-stub rooted instance and an
M-edge yz at distance D = d_B(y,z):

    (SE1)   D ≤ 2s ;         (SE2)   2D ≤ 2s + d .

**Empirical status.**  SE1 and SE2 hold with **zero violations** on: all
valid one-stub instances with n ≤ 8 and unbounded |M| (7,940 edge
checks each); n ≤ 9 with |M| ≤ 3 (89,016 edge checks each, plus 136,712
charging-bound and bridge-lemma checks); the thin-corridor exhaustive
families s = 2 (d ≤ 13), s = 3 (d ≤ 11); ~1.1M random rooted instances
12 ≤ n ≤ 16.  Moreover
they trace the exact realizability frontier of |M| = 1 signatures
(`rl_m1_frontier.py`, exhaustive n ≤ 11, 19 realizable (s, D) pairs):
the minimum d at which (s, D) is realizable is exactly d = 2(D − s)
when s < D (SE2 tight, e.g. (s,D,d) = (2,4,4), (3,6,6), (6,8,4),
(7,8,2)), and D = 2s is attained (SE1 tight) at the alternating-ladder
instances, e.g. the θ-graph witness of signature (7, 25, 4).

**Theorem 5.1 (SE1 and SE2 for corridor M-edges; PROVED; any |M|).**
Let both endpoints of an M-edge lie on some w–x₀ geodesic P: y = u_a,
z = u_b, a < b.  Then:

    D = b − a ≤ 2·#{f ∈ F : a(f) ∈ [a, b]} ≤ 2s     (SE1),

and since also D ≤ d trivially, 2D ≤ 2s + d (SE2).

*Proof.*  D = d_B(u_a,u_b) = b − a since P is geodesic.  This M-edge
crosses every level r ∈ (a, b] (Lemma 4.3's criterion with a(y) = a,
a(z) = b), and (a, b] ⊆ [1, d].  Apply the charging lemma 4.4 with
W = (a, b] (other M-edges only increase b_r): b − a ≤
2·#{f : a(f) ∈ [a, b]}.  For SE2: D ≤ d and D ≤ 2s give 2D ≤ 2s + d.  ∎

**Theorem 5.2 (SE2 when the stub pair lies on an M-geodesic; PROVED;
any |M|).**  Suppose w and x₀ both lie on some y–z geodesic Q, yz ∈ M.
Then d ≤ 2(n − 1 − D), i.e. 2D ≤ 2s + d.

*Proof.*  Run the corridor framework rooted at y with corridor Q:
levels ρ(·) = d_B(y, ·); Q is level-aligned (ρ(q_j) = j for Q's j-th
vertex), F′ := V∖Q has |F′| = n − 1 − D.  The M-edge yz crosses every
ρ-level r ∈ [1, D].  The stub pair: w, x₀ ∈ Q at positions
π_w, π_x with |π_w − π_x| = d (Q geodesic).  The level cut
Λ′_r = {ρ ≥ r} separates w from x₀ iff r ∈ W := (π_w ∧ π_x, π_w ∨ π_x],
and |W| = d, W ⊆ [1, D].  RFC† at Λ′_r for r ∈ W:
e_M(δΛ′_r) + 1 ≤ b′_r with e_M ≥ 1, so b′_r ≥ 2; by Lemma 4.1 (applied
to root y and geodesic Q — the only Q-vertices at levels r−1, r are
q_{r−1}, q_r) the second edge has an endpoint in F′ at level r−1 or r.
Charge as in 4.4: each f ∈ F′ absorbs ≤ 2 charges.  Hence d = |W| ≤
2|F′| = 2(n − 1 − D).  ∎

**5.3 Off-corridor endpoints: the framework and the precise obstruction.**

Let Q be a y–z geodesic and decompose it against the corridor P.  Since
sub-paths of geodesics are geodesics and P realises corridor distances,
Q's visits to P occur at monotone positions j₁ < ⋯ < j_t, and Q consists
of: an initial segment y ⇝ u_{j₁} of length α with interior (and y, if
y ∈ F) in F; corridor rides and F-excursions between consecutive visits
— an excursion between positions j < j′ has length exactly j′ − j (geodesy)
and j′ − j − 1 ≥ 1 interior F-vertices; and a final segment
u_{j_t} ⇝ z of length β.  Writing G for the total excursion gap,
E for the number of excursions, and "ridden" for corridor edges used:

    D = α + β + G + ridden,      q := |Q ∩ F| = α + β + G − E,

so SE1 (D ≤ 2s = 2q + 2r, r := |F∖Q|) reduces to the **ledger**

    (L)   ridden + E  ≤  q + 2r .

* When y, z ∈ P: α = β = G = E = 0 and (L) is Theorem 5.1.
* When Q avoids the corridor entirely (t ≤ 1): ridden = E = 0 and (L)
  is trivial — the "horizontal" M-edges (e.g. the witness of signature
  (6,25,2)) are paid for by their own cycle vertices q.
The interaction case is closed by the following theorem.

**Theorem 5.3 (symmetric component ledger; PROVED; second hostile audit
PASS).**  Let a connected finite graph satisfy the symmetric cut condition

    [T separates w,x₀] + [T separates y,z] ≤ e_B(δT)

for every vertex set `T`.  For geodesics `P:w--x₀` and `Q:y--z`, the ledger
`ridden+E≤q+2r` holds.  Consequently `D≤2s`; exchanging the two terminal
pairs gives `d≤2(n-1-D)`, equivalently `2D≤2s+d`.

*Proof summary.*  Delete `P` and consider each component `C` of the remaining
graph.  If its extreme attachments to `P` are `l_C,h_C`, geodesicity and a
simple path through the `|C|` vertices give `h_C-l_C≤|C|+1`.  Every corridor
edge ridden by `Q` lies in some such attachment interval: otherwise it is a
bridge, whose unit cut would separate both demand pairs and violate the cut
condition.  Assign each ride to a covering component.  Excursion gap
intervals through `C` are disjoint from rides, so

    |R_C|+G_C ≤ h_C-l_C ≤ q_C+r_C+1.

With `qexc_C=G_C-E_C`, this yields
`|R_C|+E_C≤q_C+2r_C` unless `qexc_C=r_C=0`.  Such an exceptional component
contains only an initial or final `Q` tail (it cannot contain both, or its
connectivity shortens `Q`).  If it is the initial tail, with first/last
corridor visits `a,c`, then

    |R∩I_C| ≤ min(c,h_C)-a ≤ q_C.

Indeed, failure forces `l_C=a` and `h_C-a=q_C+1`; a path inside `C` to an
attachment at `h_C`, followed by `P[h_C,c]`, is then strictly shorter than
the geodesic `Q[y,c]`.  The final-tail case is symmetric.  Summing the
component bounds proves (L), and `D=q+E+ridden`, `s=q+r` give SE1.  The cut
condition is symmetric, so applying the same argument after exchanging the
pairs gives SE2.  The zero- and one-intersection cases are immediate from
vertex counts.  The complete self-contained proof, the exact counterexample
that killed the first exceptional-tail claim, and every audit node appear in
`gap_ga_component_ledger.md` and `gap_ga_audit.md`.  ∎

Two proved special cases beyond 5.1/5.2 corroborate (L):

**Lemma 5.4 (pendant appendage rigidity; PROVED).**  If F induces a
pendant path (appendage) attached at u_j and z is its tip with M-edge
z u_b, then RFC forces b = j (the M-edge anchors exactly at the
attachment) — whence D = length of the appendage ≤ s and SE1, SE2 hold
with room.  *Proof.*  Suffix cuts S_k give (k ≤ b ⟹ appendage edge into
the suffix): capacity 1 + [j ≥ k], demand [b ≥ k] + 1, so b ≤ j; suffix
cuts S_k ∪ (whole appendage) give capacity 1 + [j < k], demand
[b < k] + 1, so b ≥ j.  ∎

**Lemma 5.5 (no free rides across bridges; PROVED).**  Corridor bridges
are never ridden by any M-geodesic (Lemma 4.5); so (L)'s "ridden" term
only accrues at corridor edges lying on B-cycles, each of which forces
F-structure nearby.  (This is the qualitative germ of the missing
quantitative step.)

---

## 6. RL for a single internal edge

**Theorem 6.1 (SE ⟹ RL, |M| = 1; PROVED; machine check C4 over the
integer box d, s ≤ 80).**  Suppose the M-edge satisfies SE1 and SE2.
Then (D+1)² ≤ s(2d + 2 + s) + 2s·p(d) — i.e. RL holds — with slack
≥ s² − 1 in case (a) and ≥ (h+1)² in case (b) below.  Only p(d) ≥ 1 is
used.

*Proof.*  M ≠ ∅ forces s ≥ 2 (Theorems 3.5, 3.6); p := p(d) ≥ 1.

*Case (a): 2s ≤ d.*  By SE1, D + 1 ≤ 2s + 1, so
(D+1)² ≤ 4s² + 4s + 1.  The RHS is ≥ s(s + 2d + 2 + 2p) ≥
s(s + 4s + 2 + 2) = 5s² + 4s.  Difference ≥ s² − 1 > 0 (s ≥ 2).

*Case (b): d < 2s.*  Let h := ⌊d/2⌋ ≤ s − 1.  By SE2 (D integral),
D ≤ s + h, so (D+1)² ≤ (s + h + 1)² = s² + 2sh + h² + 2s + 2h + 1.
The RL right-hand side is s² + 2sd + 2s + 2sp, so

    RHS − LHS = 2s(d − h) + 2sp − (h + 1)²
              ≥ 2sh + 2s − (h + 1)²        [d − h = ⌈d/2⌉ ≥ h; p ≥ 1]
              = (h + 1)(2s − h − 1)
              ≥ (h + 1)·s > 0              [h ≤ s − 1].  ∎

**Theorem 6.2 (status of RL for |M| = 1).**

* **PROVED outright.**  Theorem 5.3 gives SE1 and SE2 for the unique
  internal edge, and Theorem 6.1 gives RL.  The tree, corridor, and `s≤1`
  results remain useful stronger local descriptions.
* Exact verification still supplies independent falsification support:
  zero violations across the complete `n≤12, |M|=1` enumeration and every
  targeted/random family in §12.

---

## 7. The large-slack regime and the inductive form RL\*

**Theorem 7.1 (PROVED).**  Let R be a valid one-stub rooted instance
with 2·s·p(d) ≥ (d + 1)².  If Conjecture Γ holds for all valid instances
on n vertices — in particular if n ≤ 13, by gate 2's exhaustive
verification — then RL holds for R.

*Proof.*  (B ∪ M, χ_B) is a valid instance on n vertices (Lemma 2.2(i)),
so Γ_int ≤ n².  By Remark 1.4, RHS_RL = n² − (d+1)² + 2sp ≥ n².  ∎

**Corollary 7.2 (RL\* coverage; PROVED).**  Under the hypothesis of RL\*
(Γ on ≤ n vertices), RL holds whenever s ≥ (d+1)²/(2p(d)).  In
particular it holds for every instance with d ≤ 2: at d = 1 the
threshold is 4/6 < 1 and M ≠ ∅ forces s ≥ 2; at d = 2 the threshold is
9/4, i.e. s ≥ 3 is covered, while s ≤ 2, d = 2, M ≠ ∅ means n ≤ 5,
where no such valid instance exists (exhaustive).  Combining 7.1 with
the n ≤ 13 exhaustive data: **RL\*'s remaining open regime is exactly**

    n ≥ 14   and   2 ≤ s < (d+1)²/(2·p(d))     (so d ≥ 3),

with |M| ≥ 2 (the single-edge case is now Theorem 6.2).

*Proof.*  Direct from 7.1 and §§3, 6.  ∎

Note the reversal exposed by Theorem 2.7: the *unconditional* hard regime
of RL is large s (conjecture-strength), but under the inductive
hypothesis large s is free and the frontier moves to the thin-corridor
regime — where the data shows extreme rigidity (max Γ_int at s = 2 is 25,
flat for 4 ≤ d ≤ 13; at s = 3 it is 50 at d = 3, then 25 at d = 4, 5 and
49 for 6 ≤ d ≤ 11 — a single edge with D = 2s, never two).  This is the
correct division of labour for a future full proof.

---

## 8. The remaining gap, exactly

**G-A (single-edge, off-corridor): CLOSED.**  Theorem 5.3 proves the
ledger and both single-edge laws.  The repaired proof is independently
audited in `gap_ga_audit.md`; no unproved uniformity or computational
extrapolation enters it.

**G-B (multi-edge aggregation): SERIES SLICE CLOSED.**  For |M| ≥ 2 the charging lemma's
per-vertex bound fails (shared F-endpoints of distinct crossing edges),
and no aggregated form of SE1/SE2 that implies RL has been found.  By
Theorem 2.7 the regime s = Θ(n), d = O(1) of G-B carries the full
conjecture: **G-B is not a technical residue — it contains the open core
up to O(N)**.  Under the RL\* hypothesis, however, G-B shrinks to the
middle regime of Corollary 7.2 (n ≥ 14, 2 ≤ s < (d+1)²/(2p)).  The known
tight families of Conjecture Γ live outside it: a balanced blow-up plus
pendant stub has d = 1 and lands in the covered regime.  So the residual
G-B excludes the self-tight configurations that killed gate 2's
candidates — consistent with the strong rigidity in the thin-corridor data.
The audited series theorem now removes every case in which an interior edge
of a chosen stub geodesic is a B-bridge and both resulting components have at
least four vertices: symmetric RFC composes cutwise, Gamma and slack split
exactly, and the RL budget is superadditive.  Thus a remaining counterexample
must satisfy the exact additional restriction

```text
for every interior stub-geodesic edge e,
  IsBridge_B(e) -> min(|A_e|,|C_e|) <= 3.
```

This is strictly weaker than saying B is 2-connected.  Bridge-free segments,
endpoint-near bridges, and the genuine multiplicity aggregation remain open;
see `gap_gb_series_findings.md` and its hostile audit.

**Candidate repairs assessed and killed/blocked.**

* Volume aggregation Σ_M D_uv + d ≤ e(B) (2-commodity/tree-style): FALSE
  in general graphs — gate 2's L¹ kill (n = 12) already violates its
  unrooted form; only the tree case (3.7) survives.
* Per-vertex load: killed by gate 2's C3 (forced hub) — no vertex-load
  aggregation can hold.
* Naive per-edge SE1/SE2 + summation: (Σ(D_i+1))² ≥ Σ(D_i+1)²
  is the wrong direction; with |M| ≥ 2 and each D_i ≤ 2s one gets only
  Γ ≤ |M|(2s+1)², far above RHS for |M| ≥ 2 at small d.  A joint bound
  (e.g. Σ_i (D_i − 4) ≤ 2s − 4 + (capacity excess)) matches all current
  data but I could not derive it from RFC; recorded as a lead, not a
  claim.

---

## 9. Corollary chain (as requested; conditional on RL / RL\*)

**Lemma 9.1 (partner admissibility; PROVED).**  If two one-stub rooted
instances are glued at their roots with crossing edge x₀¹x₀² admissible
(d₁ + d₂ even and ≥ 4), then d₂ ≥ p(d₁) and d₁ ≥ p(d₂).

*Proof.*  d₂ is an admissible partner distance for d₁; p(d₁) is the least
such (Definition 1.3).  ∎

**Theorem 9.2 (RL ⟹ pair inequality, k = 1; PROVED).**  Let R₁, R₂ be
valid one-stub rooted instances satisfying RL, with admissible
d₁ + d₂.  Then

    Γ₁ + Γ₂ + (d₁ + d₂ + 1)²  ≤  (n₁ + n₂ − 1)²  −  2 s₁ s₂ .

*Proof.*  Write N = n₁ + n₂ − 1 = (d₁ + d₂ + 1) + s₁ + s₂.  Expand:

    N² − (d₁+d₂+1)²
      = (s₁+s₂)² + 2(s₁+s₂)(d₁+d₂+1)
      = s₁(2d₁+2+s₁) + s₂(2d₂+2+s₂) + 2s₁d₂ + 2s₂d₁ + 2s₁s₂ .

RL bounds Γ_i ≤ s_i(2d_i+2+s_i) + 2 s_i p(d_i) ≤ s_i(2d_i+2+s_i) +
2 s_i d_{3−i} (Lemma 9.1).  Sum and compare.  ∎

**Theorem 9.3 (no singly-crossed cut vertex; PROVED given RL, or given
RL\* within a minimal counterexample).**  Assume RL.  Then no valid
instance (G, χ) whose cut graph B has a cut vertex w crossed by exactly
one M-edge violates Conjecture Γ.  Assuming only RL\*: no *minimal*
counterexample to Γ has such a cut vertex.

*Proof.*  Let V = V₁ ∪ V₂, V₁ ∩ V₂ = {w} be a split at w, and uv the
unique crossing M-edge, u ∈ V₁, v ∈ V₂.  By gate 2's equivalence theorem
(§2.3 there; the direction needed here is the easy restriction: for
T ⊆ V_i∖{w} the global flip condition specialises to RFC of the block
with σ = the crossing stubs, since the far endpoint of the crossing edge
lies outside T), each block (B_i, M_{ii}, w, x₀ = near endpoint) is a
valid one-stub rooted instance; distances add across w:
d_B(u,v) = d₁ + d₂ with d_i the block stub distances, and block distances
agree with global ones (no path shortcuts through the other side without
repeating w).  The crossing edge is admissible (d₁ + d₂ = d_B(u,v) even
≥ 4 by S4/S5).  Also Γ = Γ₁ + Γ₂ + (d₁+d₂+1)².  By RL on each block and
Theorem 9.2, Γ ≤ N².  For the RL\* variant: in a minimal counterexample
on N vertices, each block has n_i ≤ N − 1 (the other side contributes
n_{3−i} − 1 ≥ 1 further vertices, and in fact ≥ d_{3−i} ≥ 1), so the
Γ-hypothesis of RL\* — Γ on all valid instances with ≤ n_i vertices —
is available by minimality of the counterexample.  ∎

Together with gate 2's unconditional Theorems 2.1 (leaf reduction) and
2.2 (crossing-free cut vertices), RL (or RL\* + minimality) removes every
articulation of B crossed by ≤ 1 M-edge from a minimal counterexample;
the multi-stub pair inequality (k ≥ 2) is the remaining block-reduction
piece (§11).

---

## 10. Lean formalizability assessment

* **Statement.**  Finite graph, RFC as a bounded quantifier over
  `Finset (Fin n)`, Γ_int a `Finset.sum` — direct to state in Lean 4 /
  mathlib (`SimpleGraph (Fin n)`, `SimpleGraph.dist`).  Per repo
  conventions (no `native_decide`): individual instances are `decide`-
  checkable but 2ⁿ-sized; n ≤ 9 certificates are borderline for kernel
  `decide` (512-subset sums per instance; the 65-signature audit is
  feasible as a compiled certificate table with a small checker, matching
  the repo's decide-certificate idiom).
* **Proved parts.**  §2 (RFC†, pendant-stub, minimal composite): finite
  set manipulations, no analysis — straightforward, ~2–4 weeks of
  formalisation effort.  §3 reductions: standard but fiddly vertex-
  deletion re-indexing (`Fin n → Fin (n−1)`); the s ≤ 1 case analyses are
  long but purely mechanical.  §4–5 charging: needs BFS levels
  (`SimpleGraph.dist` API exists), the "edges join consecutive levels in
  bipartite" lemma, and a double-counting argument — all elementary; the
  charging lemma is a clean `Finset.card` bound via an injection-with-
  multiplicity-2, formalizable.  §6 algebra: `nlinarith`/`polyrith`
  territory, trivial.  §7: trivial given a formal statement of Γ as a
  hypothesis.
* **Blockers.**  A complete formal proof of RL is blocked by G-A/G-B
  (mathematically open), and RL\*'s conditional form would formalise as
  an implication with the Γ-hypothesis as an explicit assumption —
  acceptable and useful as a banked reduction.
* **Recommended Lean target (bankable now).**  (i) RFC†/pendant-stub/
  composite equivalence (§2); (ii) Theorem 9.2's algebra; (iii) the s ≤ 1
  rigidity; (iv) the 65-signature RL certificate at n ≤ 9 as a decide-
  style audit.  These are self-contained and match the repo's axiom-gate
  discipline.

---

## 11. Multi-stub generalisation: what k ≥ 2 would need (sketch only)

The k-stub analogue must bound Γ_int against the full vector
(d₁, …, d_k) of stub distances — gate 2 §2.4 proves no single scalar per
block can work.  The natural target implied by the pair-inequality
algebra is

    Γ_int ≤ Σ_j s_j-terms + pairwise corrections,  concretely:
    Γ_int + Σ_j (d_j + t_j)² ≤ (n − 1 + Σ_j t_j)²  for all t ∈ [0,1]^k
    is FALSE (gate 2, C6/C7); instead one needs the direct form
    Γ₁ + Γ₂ + Σ_j (d¹_j + d²_{π(j)} + 1)² ≤ (n₁+n₂−1)².

What survives from this gate's machinery: (a) Gale–Hoffman gives k
edge-disjoint stub paths to w (Prop 2.3 with M ≠ ∅ dropped — the
σ-projection of RFC is single-commodity, so integral routing of all k
stubs exists); the corridor framework then generalises to a *Steiner
corridor* (union of the k routed paths), with slack
s := n − |Steiner corridor|; (b) the charging lemma survives per level
cut of each stub geodesic but the stub demands now stack: level cuts
carry demand 1 + #{stubs separated}, so b_r ≥ 1 + (that), giving
*more* forced F-structure — the analogue of SE1 should read
D ≤ 2s + (interaction terms in the pairwise distances d(x_i, x_j));
(c) the K₂,₂ double-stub obstruction (4, 0, (2,2)) shows the
interaction term is genuinely needed: there d₁ = d₂ = 2, s = 1, and
validity holds with M = ∅ only — consistent with a conjectural
"joint rigidity" s ≤ 1 ⟹ M = ∅ for all k, which my k = 1 proof
(Theorem 3.6) suggests generalises by the same suffix-cut analysis run
along each stub geodesic.  A worked k = 2 attempt should start exactly
there.  **Not attempted further, per the gate memo.**

---

## 12. Verification inventory (all exact arithmetic, ≤ 2 cores)

Scripts in `compute23/gate3/`; `common.py` utilities re-used from gate 2.

| script | what it verifies | range | log | result |
|---|---|---|---|---|
| `rl_enumerate.py` | RL on every valid one-stub instance; signature/slack tables | n ≤ 9, \|M\| ≤ 2 (gate-2 superset, no tri filter) | `logs_enum_n9_m2.txt` | 148,332 instances, **65 signatures** (bit-for-bit gate 2), 0 violations |
| 〃 | 〃 with B∪M triangle-free, unbounded \|M\| | n ≤ 9, all M | `logs_enum_n9_mall_tri.txt` | identical totals (no valid \|M\|≥3 instance exists ≤ 9), 0 violations |
| 〃 | 〃 | n ≤ 10, \|M\| ≤ 2 | `logs_enum_n10_m2_tri.txt` | 1,472,126 instances, 96 signatures, 0 violations |
| 〃 | 〃 | n ≤ 11, \|M\| ≤ 2 | `logs_enum_n11_m2_tri.txt` | 17,527,374 instances, 137 signatures, 0 violations |
| 〃 | 〃 | n ≤ 12, \|M\| = 1 | `logs_enum_n12_m1_tri.txt` | 144,306,516 instances, 148 signatures, 0 violations |
| `rl_steps.py` | Lemmas 3.1–3.4 (deletions/moves), 3.5–3.6 (s ≤ 1), 3.7 (trees), 4.2 (attachment), suffix-cut inequalities, Theorem 2.6 (pendant stub) | n ≤ 9, \|M\| ≤ 2 | `logs_steps_n9_m2.txt` | 0 failures (n ≤ 9 counts: 147,378 leafdel; 78,586 mleafdel; 18,929 + 18,929 root/stub moves; 234,540 attach/suffix; 3,638 pendant) |
| `rl_se_verify.py` | SE1, SE2, charging bound G1, bridge lemma MSL — per M-edge, per geodesic | n ≤ 8 all M; n ≤ 9 \|M\| ≤ 3 | `logs_se_n9_m3.txt` | 0 failures (89,016 SE1/SE2 edge checks; 136,712 G1/MSL checks at n ≤ 9) |
| `rl_corridor.py` | exhaustive thin-corridor families: max Γ_int vs RL bound | s = 2: 4 ≤ d ≤ 13; s = 3: 4 ≤ d ≤ 11; \|M\| ≤ 3 | `logs_corridor_s2_d4_9.txt`, `logs_corridor_s2_d10_14.txt`, `logs_corridor_s3.txt` | max Γ = 25 (s = 2, all d) and 25 / 49 (s = 3, d ≤ 5 / 6 ≤ d ≤ 11): single edge with D ≤ 2s, flat in d; 0 violations |
| `rl_m1_frontier.py` | realizable (d, s, D) triples, \|M\| = 1 | n ≤ 11 | `logs_m1_frontier_n11.txt` | 19 (s, D) pairs; frontier = exactly SE1 ∧ SE2 (min d = 2(D−s) for s < D); 0 SE violations |
| `rl_random.py` | RL + SE1 + SE2 on fresh random rooted instances | n ∈ [12,16], 10,000 trials, seeds 20260710/314159 | `logs_random_n12_15.txt`, `logs_random_n13_16.txt` | 1,097,960 rooted instances, 0 failures |
| `rl_misc_checks.py` | C1 composite equivalence (65 witnesses); C2 RFC† (4,622 cases); C3 RHS identities; C4 Theorem 6.1 algebra (d,s ≤ 80) | as stated | (stdout) | 0 failures |
| `rl_inspect.py` | witness decoder (θ-graph etc.) | ad hoc | — | — |

**Bottom line.**  Lemma RL is *proved* on: every `|M|=1` instance; trees;
s ≤ 1; and (given Γ on ≤ n vertices — unconditional for
n ≤ 13) the whole regime 2sp(d) ≥ (d+1)².  It is *machine-verified with
zero violations* everywhere tested (~162M exhaustive + targeted +
~1.1M random instances).  It is *not fully proved*: gap G-B (multi-edge aggregation — which
Theorem 2.7 shows contains the conjecture's open core up to O(N), so no
elementary proof should be expected).  The correct bankable target
going forward is RL\*, for which the open region is exactly
n ≥ 14, 2 ≤ s < (d+1)²/(2p(d)), |M| ≥ 2.
