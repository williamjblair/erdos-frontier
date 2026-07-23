# Erdős #617 (r=5, n=26) — search log

Ground truth: `core.py` (`is_counterexample`). Objective used everywhere:
`obj = Σ_{6-sets S} #(colors missing among S's 15 edges)` — equals
`core.violations` (Σ_c #independent-6-sets of class c). `obj = 0` ⟺ counterexample.

## W2 — stochastic local search (`sls.c`)

Engine: C, exact incremental objective. State = 325 colors. Move = pick random
violated 6-set S + missing color b; recolor one of S's 15 edges to b
(best-of-`sample_k` violated sets, delta-evaluated exactly over the 10,626
6-sets containing the edge; tabu on undoing recent recolors with tenure
`10 + nviol/64 + rand(10)`; aspiration on new global best; `noise` prob of a
random repair edge instead of best). Reload global best + 2–5 random-edge
perturbation after `reload_after` stagnant moves or drift > best+`drift`.
Consistency self-check (full recount) every 20M moves. Scoring cross-checked
exactly against `core.violations` on random colorings (3/3 match, plus probes).

Throughput ~2.7k moves/s per chain (each move ≈ up to 60 exact delta evals).

History of engine iterations (all logged, failures included):
- v1 Metropolis SA (T0 0.35–0.8): froze — single-edge deltas here are
  O(50–500), acceptance collapsed (624 accepts / 23M proposals). Discarded.
- v2 WalkSAT best-of-15-in-one-set: drift far above best (2428 vs 908).
- v3 (current) TabuCol-style best-of-4-sets + reload: robust.

Seeds: `0` uniform random; `1` random {6,5,5,5,5} clique-partitions/color
(structurally doomed per coordinator's K6-free lemma — kept only as probe);
`2` AG(2,5)-based valid K_25 (color 0 = rows∪cols rook graph, colors 1–4 =
slope parallel classes) + random 26th vertex; `3` random circulant
(difference classes on Z_26).

### Results (probes 150 s + production 4×4 h chains)

| seed | start obj | best obj reached |
|------|-----------|------------------|
| AG25 | ~4,100 | 813 |
| random | ~43,000 | 808–815 |
| circulant | ~45,000 | 783 |
| clique-partition | ~25,000 | (frozen engine v1; dropped) |

Universal plateau at **obj ≈ 780–815** from every seed family, reached in
~2 min, then no improvement for hours of aggregate chain time. Production
chains: `runs/p{1..4}.log`, best colorings in `runs/p*_*.best.txt`.

### Plateau autopsy (the key structural finding)

For the plateau solutions analyzed: **every violated (S,c) contains one fixed
pair of vertices** {u,v} (e.g. {2,23} in `pC.best.txt`, 814/814 violated sets).
Contracting v into u yields a **valid K_25 coloring** (0 bad 6-sets, verified
exhaustively). So the local search always terminates at:
  valid K_25 coloring + one vertex split into "near-twins", with the split
  pair uncoverable.
Class structure of one harvested K_25: sizes (60,51,62,62,65) — NOT the AG
structure (100,50,50,50,50); the valid-K_25 space is richer than the affine
family.

## W3 — completion / extension SAT (exact, CaDiCaL 1.9.5 via pysat)

`w3_completion.py`: freeze best coloring outside a freed vertex set F, free
all edges touching F, exact SAT on the rest.
On `pC.best.txt` (obj 814, bad pair {2,23}):

| freed vertices | free edges | result | time |
|---|---|---|---|
| {2,23} | 49 | UNSAT | 0.0 s |
| {2,23,16,17} | 94 | UNSAT | 0.2 s |
| +{12,15} (6) | 135 | UNSAT | 1.8 s |
| +{21,19} (8) | 172 (53% of all edges) | UNSAT | 38.7 s |

I.e. the fixed 18-vertex interior already forbids ANY completion of the other
8 vertices.

`w3_extend.py`: a valid K_26 coloring restricted to any 25 vertices is a valid
K_25 coloring, so K_26 SAT ⟺ some valid K_25 coloring is 1-vertex-extendable.
Extension test per K_25 coloring = 125-var SAT. Results: AG construction →
UNSAT 0.00 s; harvested SLS K_25 → UNSAT 0.00 s.

`w3_certificate.py`: counting certificate. For attach vertex w, per color c,
H_c = N_c(w) must (i) hit every independent 5-set of class c, (ii) contain no
5-clique of class c (else mono-K_6); the H_c partition the 25 vertices. With
h_c = min admissible |H|: Σ_c h_c > 25 ⟹ non-extendable.

| K_25 coloring | class h_c values | Σ h_c |
|---|---|---|
| AG(2,5) rook+4 classes | 8,25,25,25,25 | 108 |
| SLS-harvested (60,51,62,62,65) | 8,8,8,8,8 | 40 |

Both ≫ 25. Conjecture worth proving (would settle UNSAT): h_c ≥ 6 for every
class of every valid K_25 coloring (then Σ ≥ 30 > 25).

## W1 — full SAT with symmetry breaking (`w1_encode.py`, `w1_solve.py`)

Encoding (n parameterized): one-hot 5×NE vars; pairwise EO per edge; coverage
clause per (6-set, color); complete color-symmetry lex-leader
(first-occurrence prefix chain); vertex lex-leader for 25 adjacent
transpositions; per-class cardinality 55 ≤ |G_c| ≤ 105 (Turán / counting,
seqcounter). n=26: 194,175 vars, 1,554,525 clauses (`runs/w1_full.cnf`).

Pipeline validation on n=25 (known SAT via AG): with vertex lex-leader,
CaDiCaL made no visible progress in ~40 min (lex-leader forces the lex-min
representative — hard); killed, relaunched without vertex lex
(`runs/w1_n25_nolex.log`) to validate the sat-side of the pipeline.

## Session 2026-07-10 ~11:20 — babysit + classification route

### Solver harvest
- **W1 n=25 nolex pipeline validation: SAT in 358 s** (CaDiCaL, 0 bad 6-sets
  on independent recheck) — the W1 encoder is validated on the SAT side.
  (The first launch died with the old session; relaunched, done.)
- **r=3 general K_10: UNSAT in 222.5 s** (Kissat404, `small_r3.log`) —
  calibration anchor vs the known theorem PASSES.
- r=4 general K_17: first run died with old session; relaunched (running).
- E7 general (fixing_sat identity, Kissat404): still running (~1 h in).
  Second opinion `general_cadical.py` (Cadical300) died with the old session;
  relaunched (running). 2^13 / 2^12-1-1 orbit-fixing: still running.
- W1 full n=26 (CaDiCaL): still running. m* edge-bound run (min edges of a
  (6,6)-Ramsey graph on 26 vts; >65 would prove UNSAT by counting): still
  running — NOTE its stdout is block-buffered into a session task file,
  output appears only at flush/exit.
- SLS p3/p4: still running to their 4 h walls, plateau 808/781, no change.
- **anneal617 ×12 KILLED** (~50 min in): best 808 = SLS plateau, strictly
  dominated by sls.c, was oversubscribing the 16-core box. Trajectories in
  `anneal_*.err`.

### CORRECTION to the W3 certificate table
The earlier AG row "h = 8,25,25,25,25" is wrong (pre-fix code). Current
`w3_certificate.py` (with the unrestricted-feasibility check): AG slope
classes are 5 disjoint K_5s, any H hitting all line-transversals must
contain a full line = forbidden 5-clique ⇒ **h_c = ∞**. AG true vector:
(8, ∞, ∞, ∞, ∞).

### Classification route (new)
- **Harvest complete**: 77 valid K_25s from sls25 (w1/w2 workers,
  `runs25/harvest.tsv`). Every one: h_c ∈ {8, ∞} per class, Σ ≥ 40,
  extension UNSAT.
- **Isomorphism classification** (`classify25.py`, invariant fingerprint +
  exact colored-iso backtracking): the 79 known valid K_25s (77 harvested +
  probe + AG) are **pairwise non-isomorphic** — 79 iso classes. The valid
  space is enormous; enumeration up to iso is hopeless. Classification
  pivots to proving the counting lemma instead.
- **Translation-invariant family COMPLETELY classified** (`trans_enum.py`):
  Z_5^2-invariant valid K_25 colorings = 16,200 raw SAT solutions =
  **exactly 2 classes** up to GL(2,5) × color perms:
  rep#0 = AG (sizes 50,50,50,50,100; h = ∞,∞,∞,∞,8);
  rep#1 = **NEW**, sizes (50,50,50,75,75), h = (∞,8,∞,∞,8). Both ext-UNSAT.
- **Local-move structure** (`freedom25.py`): edge e recolorable keeping
  validity ⟺ every 6-set ∋ e has ≥2 edges of e's color. Every sampled
  non-AG valid K_25 has **exactly 50 free edges** (= 300 − 5·50 Turán
  excess); AG has 100 (its whole rook class). The valid space is NOT rigid:
  every point has 200–400 single-edge neighbours.
- **Random walks in the valid space** (`walk25.py`, >1100 accepted moves per
  chain): h stays (8,8,8,8,8) almost everywhere, **but 25 steps from AG a
  class with h_c = 5 appears** (h = 5,8,8,8,8, Σ = 37, ext still UNSAT).
  ⇒ the clean sub-lemma "h_c ≥ 6 always" is **FALSE**. The viable lemma is
  Σ_c h_c > 25 itself. Empirical min Σ so far: **37** (budget 25).
- **Target-lemma SAT** (`lemma_h6_sat.py`): single instance asking
  "∃ valid K_25 with class-0 h ≤ B" (995,275 clauses; encoder property-
  tested: flips SAT/UNSAT exactly at the independently computed h = 8 on a
  harvested coloring). B=5 launched — given the walk's h=5 find it should
  return SAT with a witness; kept running for confirmation.
- **Σh descent** (`hclimb25.py`, 3 chains): hill-climb on Σ h_c over the
  valid space via free-edge moves; any Σ ≤ 25 triggers immediate extension
  SAT + core verification. Running; all chains floor at exactly 37 =
  5 + 4·8, corroborating the one-cheap-class picture below.
- **Cheap-class anatomy** (h=5 witness `runs25/hclimb_ag.best.txt`): the
  h=5 class is the degraded rook class — 94 edges, only 270 ind-5-sets,
  H = one grid line {0,5,10,15,20} (no longer a 5-clique after the walk
  removed line edges). Cheap ⟹ BIG: sizes (94,52,51,51,52). Edge budget
  (300 total, 50 floor/class) then forbids ≥2 cheap classes if cheap ⟹
  ≥76 edges (2·76 + 3·50 = 302 > 300).
- **Decomposed lemma instances** (`lemma_variants.py`, all launched under
  Kissat404, ~1–1.4M clauses each):
  - LEMMA-A `edges 75`: valid K_25 + class-0 h ≤ 5 + |E_0| ≤ 75.
    UNSAT ⟹ at most one cheap (h≤5) class per valid K_25.
  - LEMMA-B `floor 1`: valid K_25 + class-0 h ≤ 1. UNSAT ⟹ h_c ≥ 2 always.
  - LEMMA-SUM `sum`: five per-class admissible H_c with Σ|H_c| ≤ 25
    (no disjointness — pure counting relaxation of E7).
    UNSAT ⟹ Σ h_c > 25 for every valid K_25 ⟹ **r=5 n=26 settled UNSAT**.
  Proof routes to the theorem: LEMMA-SUM alone, or (LEMMA-A ∧ LEMMA-B:
  Σ ≥ 2 + 4·6 = 26 > 25), or E7 directly. Three independent jugulars now
  in flight.
- E3 (5^5·1 cycling, hardest symmetric family) had died with its session —
  relaunched.
- **Certification prep**: exact E7 instance dumped to `runs/e7_general.cnf`
  (1625 vars, 1,154,726 clauses, DIMACS). pysat's Kissat404 exposes no
  proof logging — the DRAT rerun on an UNSAT verdict needs a standalone
  kissat (`brew install kissat` or build), then
  `kissat --no-binary runs/e7_general.cnf runs/e7_general.drat`.

## Session 2026-07-10 ~12:30 — P0 affine residual, silence semantics, bounds, proof logging

### P0 — E9 affine residual model: FAMILY EMPTY (exact SAT, all 6 choices)
`e9_affine_residual.py` (+ selftest: 6 direction classes x 50 edges, each 5
disjoint K_5s). V = F_5^2 ∪ {∞}; omit one direction, fix the other 5 as the
colors (bijection WLOG by color symmetry), SAT the 75 free edges (omitted 50
+ ∞ 25) against full (6-set, color) coverage. **All 6 omitted-direction
completions UNSAT in ~0.1 s each** (`e9_affine.log`). Structural fact: after
fixing, exactly 5^6 = 15,625 coverage clauses survive — within-plane 6-sets
are auto-covered for every kept color (pigeonhole on 5 parallel lines), so
the ONLY binding constraints are S = {∞} ∪ (transversal of the 5 c-lines),
5^5 per color; 75 free edges cannot hit them all. This machine-confirms the
E5 hand proof (omit = vertical) and extends it to all 6 directions
(consistent with AGL(2,5) transitivity on P^1(F_5); identical clause counts
across all 6 instances corroborate).

### P1 — silence semantics (Lemma-B repair)
A class can be SILENT (alpha <= 4): zero independent 5-sets ⟹ H = ∅ is
admissible ⟹ h = 0. So `lemma_variants.py floor 1` (still running) asks
"silent class OR loud class with h<=1" — its SAT verdict would be
uninformative without an autopsy; only UNSAT is directly usable (and even
then the loud-conditioned form is the right lemma). The corrected,
loudness-conditioned instances (`lemma_loud.py`, launched 12:22) are the
trusted line: `floor_loud 1` (loud ⟹ h >= 2), `silent` (is s >= 1
inhabited?), `double_silent` (danger cube s=2, where 0+0+3·8 = 24 <= 25
defeats the counting certificate), plus `silent_floor.py 75` (isolated
probe: silent floor >= 76 ⟹ s <= 1 by 2·76 + 3·50 > 300). Cube arithmetic
uses the hand bounds: silent ⟹ >= 67 edges (66 forces complement =
T(25,4) = K_{7,6,6,6} by Turán uniqueness ⟹ G = K_7+3K_6 ⊇ K_6, dead);
loud floor 50; 3·67 + 2·50 = 301 > 300 ⟹ s <= 2.

### P3 — new cardinality bounds (n=26 ONLY; do not port to K_25 — AG has
six edge-disjoint 5-clique covers, so the pigeonhole fails on 25 pts)
(i) every class >= 56 (55-edge extremum is the {6,5,5,5,5} clique partition
⊇ K_6); (ii) at most one class has a 5-clique cover (E4 pigeonhole), the
rest have non-5-partite K_6-free complements ⟹ <= 266 edges (Brouwer 1981:
ex(26,5) − ⌊26/5⌋ + 1) ⟹ class >= 59; so >= 4 classes >= 59, aggregate
>= 4·59 + 56 = 292, slack <= 33; (iii) every class <= 92. Encoded in
`e7_bounded.py`: base E7 + per-class atleast-56/atmost-92 + selectors a_c
(pairwise a∨a = at-least-4) with conditionalized atleast-59 networks.
**Encoder property-tested 5/5** (SAT/UNSAT flips exactly at floor 56, cap
92, and two-classes-below-59). Dumped `runs/e7_bounded.cnf` (263,120 vars,
1,675,281 clauses); standalone kissat running (`runs/e7_bounded_kissat.log`).
UNSAT here = theorem modulo side lemmas (i)–(iii); the unbounded E7 stays
as the assumption-free line. TODO: port bounds into `w1_encode.py` before
any w1 restart (running w1 still has the old 55..105).

### P4 — proof-logging toolchain
Built from source in `tools/`: **kissat 4.0.4** (`tools/kissat/build/kissat`)
and **drat-trim**. Calibration COMPLETE on the r=3 K_10 anchor: `runs/r3_k10.cnf` dumped
(same encoding as `smallcase_sat.py`, 135 vars / 811 clauses), standalone
kissat UNSAT in ~110 s CPU (pysat baseline 222.5 s), DRAT proof 141 MB,
**drat-trim: s VERIFIED** (781/811 clauses in core, 2.17M of 2.88M lemmas,
57.8M resolution steps, 297 s). The certification pipeline is proven
end-to-end. NOTE the proof-size scaling: 141 MB for an 811-clause instance;
an E7-scale proof will be O(100 GB); disk has only 38 GiB free. Endgame
plan: verdict first without logging, then a dedicated DRAT rerun with disk
cleared, or stream kissat straight into a checker via a FIFO.

### Harvest / culls (~12:30, box was at load 68 on 16 cores)
- CULLED: sls p3/p4 (plateau 781/808 for hours, autopsy long done) and
  `general_cadical.py` (E7 second opinion; Kissat404 `fixing_sat` identity
  stays primary; bounded E7 is now the second line). Logged, freed 3 cores.
- Still running, no verdicts yet: E7 general (kissat, ~2 h), w1 full n=26,
  fixing 2^13 & 2^12-1-1, e3 (5^5·1 cycling), r=4 K_17 general,
  lemma_variants edges/floor/sum (~1 h), lemma_loud x3 + silent_floor
  (~10 min), hclimb_a, m* edge-floor probe (block-buffered, output at exit).

## Status / read (updated 2026-07-10 ~12:50)

- No witness. All claimed results verified against `core.py` where applicable.
- Read: **strongly leaning UNSAT.** Every seed family funnels to the same
  "valid K_25 + irreducible split pair" plateau at obj ≈ 800; exact SAT
  completion around the defect (up to 53% of edges freed) is UNSAT in seconds;
  every valid K_25 examined (79 pairwise non-isomorphic + the 2-member
  complete translation-invariant classification + >2200 walk steps) is
  non-extendable, Σ h_c ≥ 37 ≫ 25; and the most structured family (E9
  affine residual, all 6 omitted directions) is exactly-UNSAT in 0.1 s each.
- Calibration anchors: r=3 general UNSAT reproduced twice (pysat 222.5 s;
  standalone kissat 4.0.4 ~2 min with 141 MB DRAT emitted), n=25 SAT.
- Cube tree (K_25 lemma route): LEMMA-SUM is the cube-free jugular (covers
  silent classes via H = ∅). Decomposed legs: s=2 killed by any of
  {double_silent UNSAT, silent_floor >= 76, silent UNSAT}; s=0 closed by
  edges_loud(5,75) UNSAT + floor_loud(1) UNSAT (<=1 cheap loud, cheap h>=2,
  rest h>=6: 2+4·6 = 26 > 25). CAUTION s=1: counting can NEVER close it —
  four louds at h>=6 give Σ = 24 <= 25 even if no cheap loud coexists with
  the silent class; s=1 dies only via silent UNSAT or the joint
  `sum_silent` instance (silent class 0 + Σ_{c>=1}|H_c| <= 25; launched
  12:55). All legs in flight.
- Jugular stack (independent routes to the theorem): (1) LEMMA-SUM UNSAT;
  (2) cube legs above; (3) E7 general UNSAT (unbounded, assumption-free);
  (4) E7-bounded UNSAT (fastest expected, modulo side lemmas (i)-(iii));
  (5) m* >= 66 by the edge-floor probe. Then a DRAT rerun for certification
  (disk: only 38 GiB free — plan the proof-logging rerun deliberately).
14:13 culled monolithic E7 x3, w1, original lemma trio (superseded/broken-semantics); cores now dedicated to: cube legs (silent, double_silent, floor_loud, edges_loud, silent_floor, sum_silent) + e7_bounded kissat
14:16 culled hclimb; launching sub-cube splitting campaign

## Session 2026-07-10 ~14:30 — cube-and-conquer sub-splitting + SMS

### Sub-cube campaign (running)
Machinery: `cube_common.py` (leg builders replicate the EXACT clause lists
of the running baselines — counts asserted against the logged values),
`graph_reps.py` (canonical reps of graphs on m vertices up to iso, counts
verified against 1,2,4,11,34,156,1044,12346), `gen_cubes.py`,
`cube_run.py` (work-queue driver: persistent Cadical195 per worker,
formula loaded ONCE, cubes = assumption sets under conflict budgets
100k -> 1M -> survivors.json; restart-safe results.tsv; SAT => in-worker
exact verification: valid_k25, silence/H-admissibility, extension SAT,
core.is_counterexample on any extension), `make_children.py` (deepen
window {0..6} -> {0..7} by vertex-7 neighborhoods up to Aut(P) orbits),
`kissat_cubes.py` (uncapped standalone-kissat stage; NOTE pysat Kissat404
IGNORES assumptions — never conquer with it).

Split: class-0 pattern on the 21 edges inside {0..6} — 1044 iso-reduced
cubes = 2^21 raw-cube coverage. SOUNDNESS (hand argument, banked): every
leg's constraint set is S_25-invariant (card networks are symmetric
functions; seqcounter aux re-extendable), so any solution relabels by a
permutation supported on {0..6} to one whose window pattern is the
canonical representative; UNSAT of all 1044 cubes => leg UNSAT.
Cube verdicts are therefore "UNSAT modulo this covering argument" —
the running monolithic legs remain the assumption-free line.

Selftest (13/13 OK, `selftest_cubes.py`): AG full-units SAT + decode ==
AG + valid; K7-complete cube UNSAT instantly; AG-pattern cube SAT in 2 s
with verified valid K_25; h=5 witness line admissible / singleton not.

Launched 14:29: sum_silent (2 workers) + edges_loud (1 worker), niced,
runs/cubes_{sum_silent,edges_loud}/. Early shape: dense patterns die by
propagation (~150/min), first UNKNOWN band at 13 edges. Leg DIMACS dumped
for reproduction: runs/leg_sum_silent.cnf (96M), runs/leg_edges_loud.cnf
(75M).

### SMS (sat-modulo-symmetries) — BUILT, CALIBRATED, PILOT RUNNING
Built from source (tools/sat-modulo-symmetries, one fix: missing
`#include <sstream>` in src/useful.h under current Xcode libc++);
binary tools/sat-modulo-symmetries/build/src/smsg with cadical_sms.
The compiled smsg has NO multi-graph mode (pysms targets a newer
feature), so the K_26 encoding breaks S_26 through the CLASS-0 lens:
SMS edge vars 1..325 = class 0, aux one-hot colors 1..4 + coverage
(`sms_encode.py`); side constraints are vertex-invariant as a set, so
restricting to lex-min class-0 representatives is exhaustive. On top:
color-symmetry first-occurrence lex chain over colors 1..4 (sound
composition: recoloring 1..4 fixes the class-0 graph).

CALIBRATION BOMBSHELL: the r=3 K_10 anchor (222.5 s pysat, ~110 s
standalone kissat) is UNSAT under smsg in **0.02 s** (runs/sms_r3_k10.log)
— ~4 orders of magnitude from native vertex-symmetry handling. SAT-side
control: n=9 r=3 (AG(2,3) parallel classes construction exists) returns
a witness, exit 10, also with the color-lex chain on. Instances:
runs/sms_r5_k26.cnf (plain), runs/sms_r5_k26_cb.cnf (color-lex; PILOT
RUNNING since ~14:45, 1 niced core, runs/sms_r5_k26_cb.log). smsg also
supports lookahead cubing (--assignment-cutoff) and LRAT output
(--lrat-output) for certification — noted for the endgame.
14:57 culled silent_floor.py + e3 (SMS supersedes)
14:58 SMS trio relaunched from persistent session (agent-spawned ones were mass-TERMed at agent exit; logs were empty): pids 66331/66332/66333, logs runs/sms_{k26,sum,sfloor}_main.log
14:59 CORRECTION: SMS trio never died - monitor kill -0 is sandbox-blocked (false exits); duplicates culled; switching liveness checks to ps -p
15:03 culled 3 baseline legs; cores to SMS trio + swarm
15:10 VERDICT: sms_silent_floor75 UNSAT (Result 20, 769.8s) => THEOREM: silent class needs >= 76 edges => s=2 cube CLOSED (2*76 + 3*50 = 302 > 300). Remaining: s=0 (edges_loud+floor_loud), s=1 (sum_silent, SMS running).
15:38 K26-direct SMS relaunched from main session (pid 96853, prior run died unflushed at ~48 CPU-min)
15:45 swarm drivers restarted under main session (resume-aware): sum pid 29630, edges pid 29631, 3 workers each
15:46 Full SMS coverage under main session: K26-direct (96853), sum_silent (19422), edges_loud (32126), floor_loud (32127) + kissat e7_bounded (7980). Swarm evidence banked (390 UNSAT / 0 SAT in results.tsv); cube lists died with agent, not regenerating - SMS supersedes.
16:49 escalation pulled forward: sum_silent in SMS cube mode (simple-assignment-cutoff 60, pid 66235) alongside plain run
