# Erdős #617 (r=5, n=26) — construction families log

GOAL: 5-color E(K_26) with every color class alpha <= 5 (every 6-set induces
all 5 colors).  Ground truth: `core.py` (`is_counterexample`, `verify_and_report`).
Turán floor: each class >= 55 edges (unique minimum = clique partition
{6,5,5,5,5}); total 325 = 5·65, slack 50.

## E1 — pure Z_26 circulant (color = f(difference))  — IMPOSSIBLE (proved, no search needed)
Difference classes: d=1..12 have 26 edges, d=13 has 13.  Class without d=13
needs >= 3 full diff classes (2·26 = 52 < 55); the d=13 class helps only one
color (2·26+13 = 65 >= 55).  Full classes needed >= 4·3 + 2 = 14 > 12
available.  Contradiction with the Turán floor.  VERDICT: family empty.

## E2 — bicirculant (order-13 symmetry, color fixed on pair-orbits)
tau = two 13-cycles (conjugate to any order-13 perm on 26 pts; e.g. the
Sylow-13 of PGL_2(25) acting on P^1(F_25)).  25 pair-orbits of size 13
(6 within cycle A, 6 within cycle B, 13 cross).  alpha<=5 forces >= 55 edges
per color -> >= 5 orbits each -> exactly 5 orbits per color.  Search space
25 orbits -> 5 colors balanced.  STATUS: pending (SAT encoding).

## E3 — sigma5-equivariant "pentagon generalization"
sigma = (+5 on Z_25)·(∞ fixed), cycle type 5^5·1 (unique usable order-5 type:
any fixed edge kills color-cycling; all such sigma conjugate, so the SAT
verdict covers the whole family).  color(sigma e) = color(e)+1 mod 5 =>
G_c = sigma^c(G_0), all classes isomorphic; problem reduces to choosing one
edge per orbit (65 orbit phases) with alpha(G_0) <= 5.
SAT: 325 vars, 230230 6-set clauses + one-hot.  STATUS: running (e3_equivariant_sat.py).

## E4 — resolvable packing design (5 edge-disjoint {6,5,5,5,5}-clique partitions)
Social-golfer-like: 26 points, 5 parallel classes, block sizes {6,5,5,5,5},
every pair together <= 1 time (uses 275 of 325 pairs).  If found: each class
contains a spanning clique partition => alpha <= 5, leftover 50 edges colored
arbitrarily => instant counterexample.
Note: no tau13-invariant design (orbit sizes 13/26 can't be blocks of 5/6, and
5-block orbits under sigma5 come in 5s but classes need 4 such blocks); pure
AG(2,5)+∞ variant impossible (attached lines from distinct parallel classes
always meet).  STATUS: running raw CP-SAT (e4_design_cpsat.py).

## E5 — AG(2,5) slope ansatz + free-edge completion — IMPOSSIBLE (proved, no search needed)
Ansatz: 25 pts = F_5^2 + ∞; color non-vertical edge by slope; vertical (50) and
∞-edges (25) free.  Analysis:
(1) 6-sets needing attention are exactly {∞} ∪ transversal of the 5 slope-c
    lines, for each class c.
(2) Line-transversals (a full line of slope s != c is a transversal for class c
    with all internal pairs colored s) force the ∞-edge coloring f: F_5^2 -> colors
    to hit all colors != s on every line of slope s.  Counting (each color's
    ∞-neighborhood must hit all lines of 4 slope classes => >= 5 points; total
    = 25) forces each color class of f to be exactly a vertical line or a
    slope-c line; disjointness forces ALL to be vertical columns: f = column color.
(3) Then for class c, unblocked transversals are those avoiding column c; the
    only remaining blockers are vertical pairs.  For ANY coloring of the 50
    vertical edges there is an unblocked transversal: pick a vertical pair
    {b,b'} independent in the color-c vertical graph of some column a != c
    (exists unless ALL 10 pairs of every column != c are colored c —
    impossible for 4 classes at once), place the other 3 line-indices as
    singletons in the remaining 3 columns.  VERDICT: family empty.

## E9 — affine residual completion (generalizes E5 to all omitted directions) — EMPTY (exact SAT)
V = F_5^2 ∪ {∞}; the 300 plane edges = 6 direction classes of 50 (each 5
disjoint K_5s).  Omit one direction, fix the other five AS the colors
(bijection WLOG by color symmetry); SAT the 75 residual edges (omitted 50 +
∞ 25) exactly against full (6-set,color) coverage.  `e9_affine_residual.py`
(selftest: class structure verified), log `e9_affine.log`.
**All 6 omitted-direction instances UNSAT, ~0.1 s each.**  Structure: only
5^6 coverage clauses survive the fixing — within-plane 6-sets are auto-
covered for every kept color (pigeonhole over 5 parallel lines), so the
binding 6-sets are exactly {∞} ∪ (transversal of the 5 c-lines), 5^5 per
color.  Confirms the E5 hand proof by machine and closes the whole
AGL(2,5)-orbit of the ansatz (omitted-direction choice is WLOG under
(x,y)->(y,x) and (x,y)->(x,x+y); the 6 runs are belt-and-braces).
VERDICT: family empty — the most structured candidate family is dead.

## E6 — Z_25-cycling colorings (translation +1 cycles the colors)
color({x,x+d}) = c_d + x mod 5 (d = 1..12 canonical diff), color({∞,x}) = c_∞ + x.
Consistency under translation forces exactly this 13-parameter form (c ∈ Z_5^13).
G_j all isomorphic (translates), so single-graph check.  Subsumed by the
cycle-type-25 cycling SAT below.  VERDICT: UNSAT (empty).

## RESULTS — color-cycling families (color(pi e) = color(e)+1 mod 5)
Requires all edge-orbit sizes divisible by 5 => pi cycle type = fixed point +
parts from {5,10,15,20,25} (7 types, each covers its whole S_26-conjugacy
class).  Single-graph SAT (alpha(G_0) <= 5, G_c = pi^c G_0), 230230 6-set
clauses; encoder validated: (a) literal/reconstruction consistency on random
phases, (b) alpha<=6 relaxation of type 25 is SAT and verifies alpha=6 exactly.
  type 25:        UNSAT (0.1s)
  type 20-5:      UNSAT (0.1s)
  type 15-10:     UNSAT (0.1s)
  type 15-5-5:    UNSAT (0.1s)
  type 10-10-5:   UNSAT (0.5s)
  type 10-5-5-5:  UNSAT (0.3s)
  type 5-5-5-5-5 (E3): pending (kissat, hardest instance)

## RESULTS — orbit-fixing families (coloring constant on edge-orbits of pi)
Encoder property-tested EXACT against core.violations (20 random assignments,
violated clauses == independent-6-set count).  All colorings invariant under
ANY permutation of each type are covered (conjugacy).  Counting pre-kills:
order-25 fixing (13 orbits of 25: needs 3 orbits/color = 15 > 13), Z_26
circulant (E1 above), 21-5 (105-orbit forces class >= 105, 220 < 4·56),
16-10 (two 80-orbits: 160 + 3·56 > 325), 14-12 (84-orbits likewise).
SAT verdicts (all Kissat404):
  13-13 (E2, incl. PGL_2(25) Sylow-13):        UNSAT (1.3s)
  24-1-1 (split torus of PGL_2(25)):           UNSAT
  22-4, 20-6, 20-5-1, 15-10-1:                 UNSAT
  12-12-1-1 (order-12 torus):                  UNSAT
  10-10-5-1:                                   UNSAT
  5-5-5-5-5-1 (sigma5-fixing, 65 orbits):      UNSAT
  8-8-8-1-1, 6-6-6-6-1-1 (57 orbits):          UNSAT
  4^6-1-1 (85 orbits), 3^8-1-1 (109 orbits):   UNSAT
  2^13, 2^12-1-1 (163/169 orbits):             running
CONSEQUENCE: no counterexample admits ANY nontrivial automorphism-with-color-
preservation of the tested orders; combined with cycling verdicts, all
cyclic-subgroup-invariant colorings for every element order of PGL_2(25)
(2,3,4,5,6,8,12,13,24,26) are dead except possibly order-2 (running) and
5^5-1 cycling (running).

## E7 — GENERAL problem, no symmetry assumption
fixing_sat.py with identity permutation = exact unrestricted question:
1625 vars, 1,154,726 clauses (one per (6-set, color) + one-hot).
If UNSAT: the r=5, n=26 instance of the conjecture is CONFIRMED outright.
STATUS: running (kissat).

## E4 — UPDATE: IMPOSSIBLE (pigeonhole proof + CP-SAT INFEASIBLE cross-check)
Any partition of 26 points into <= 5 cliques has a part with >= 6 points
(5·5 < 26); those 6 points meet the <= 5 parts of any other such partition in
>= 2 common points somewhere => a pair covered twice.  So even TWO edge-
disjoint 5-clique-partitions cannot coexist.  CP-SAT independently returned
INFEASIBLE in 0.3s.  Moreover any class containing K_6 is dead outright
(the K_6's 6-set is independent in every other class), so minimal 55-edge
classes (= clique partitions) are impossible: every class is a (6,6)-Ramsey
graph on 26 vertices with 56..(325-4·56) edges.

## Small-case calibration (same problem shape, K_{r^2+1}, r colors, alpha<=r)
r=2 (K_5): EXISTS — pentagon/pentagram, a circulant(=fixing) solution.
r=3 (K_10): circulant impossible by the same granularity counting as E1;
  cycling types 3-3-3, 3-6, 9: all UNSAT.
  **General K_10 SAT: UNSAT (222.5s, Kissat404)** — reproduces the known
  theorem, validates the general-instance pipeline end to end.
r=4 (K_17): cycling types 16, 8-8: UNSAT (others undefined, orbit sizes).
  General K_17 SAT: running (relaunched 2026-07-10; first run died with its
  session).

## E8 — valid K_25 landscape (classification route, 2026-07-10)
The K_26 question ⟺ some valid K_25 (5-coloring of E(K_25), all classes
alpha<=5, hence K_6-free) is 1-vertex-extendable.  Findings:
- **Z_5^2-translation-invariant valid K_25s: completely classified.**
  12 difference-pair orbits, 60-var SAT, 16,200 raw solutions, exactly
  **2 classes** up to GL(2,5) x color perms: AG(2,5) slope coloring
  (50,50,50,50,100) and a NEW one (50,50,50,75,75) with two 3-orbit classes.
  Both non-extendable (h certificate + extension SAT).  `trans_enum.py`.
- 79 valid K_25s known so far are pairwise NON-isomorphic (`classify25.py`):
  the space is vast, enumeration hopeless; the route's value is the
  counting-lemma target, not a catalogue.
- Every valid K_25 has free edges (50 of them; AG 100): the space is
  locally flexible, single-edge moves reach far (walks of >1100 moves).
- h_c spectrum seen so far: {5, 8, ∞} only; Σ h_c min seen 37 > 25.
  "h_c >= 6 always" is FALSE (h=5 class 25 moves from AG) — the lemma to
  prove is Σ_c h_c > 25 directly (or E7 UNSAT outright).
