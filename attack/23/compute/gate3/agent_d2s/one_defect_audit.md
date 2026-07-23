# Hostile audit: Erdős 23 `d = 2s-1` one-defect boundary

Verdict: **PASS for the exact deficit classification, span-defect
elimination, sharpened resource arithmetic, and RFC landing theorem.**
The mass-defect and overlap-defect cut construction is not proved, so this
file does not claim the `d=2s-1` BF-RL slice is closed.

## Kernel-checked progress

The new source is
`ErdosProblems/Erdos23GapGBOneDefect.lean`.

### 1. Exact deficit identity and trichotomy — PASS

For canonical components `C`, put

```text
q_C = |C|,
I_C = the extreme-attachment edge interval,
m = number of components,
U = union_C I_C.
```

The source proves the exact natural-number identity

```text
(s-m)
+ sum_C (q_C+1-|I_C|)
+ (sum_C |I_C|-|U|)
= 2s-|U|.
```

All three terms are nonnegative for explicit reasons: positive component
mass, the geodesic attachment-span bound, and the finite-union cardinality
bound. When every corridor edge is a nonbridge, the canonical intervals
cover the corridor, and each interval is contained in it, so `U=[0,d)`.
At `d=2s-1`, exactly one displayed deficit is one.

Kernel:

- `intervalDefect_identity`;
- `intervalDefect_one_trichotomy`;
- `IsGeodesic.canonical_oneDefect_trichotomy`.

### 2. Three defect geometries — PASS

- **Mass defect:** `m=s-1`; exactly one component has mass two and every
  other component has mass one. Zero span deficit saturates every interval,
  and zero overlap deficit makes the intervals pairwise disjoint. Thus the
  corridor is partitioned into one length-three interval and length-two
  intervals.
- **Span defect:** all components are singleton; exactly one interval has
  length one and every other interval has length two; zero overlap makes them
  pairwise disjoint.
- **Overlap defect:** all components are singleton, every interval has length
  two, and total interval multiplicity exceeds the union by exactly one.

Kernel:

- `massDefect_structure`;
- `spanDefect_structure`;
- `overlapDefect_structure`;
- `pairwiseDisjoint_of_overlapDefect_eq_zero`.

### 3. Span defect is impossible in the bipartite instance — PASS

A singleton component with interval length one is adjacent to both endpoints
of a corridor edge. Those three edges form an odd triangle and contradict a
proper Boolean coloring. The proof uses the actual minimum and maximum
attachment witnesses, not an asserted picture.

Kernel:

- `no_singleton_offCorridorComponent_span_one`;
- `canonical_spanDefect_case_false`.

Consequently only the mass-defect and overlap-defect geometries survive.

### 4. Sharpened `|M|>=2` arithmetic — PASS

Let positive resources `r_i` satisfy `R=sum_i r_i<=s-1`, with at least two
demands and `D_i<=2r_i+2`. A second positive demand gives `r_i<=R-1` for
every `i`, hence

```text
sum_i r_i^2 <= R(R-1).
```

Expanding every quadratic cost and using `s>=5` gives exactly

```text
sum_i (D_i+1)^2 <= rlBudget(s,2s-1) = 5s^2+2s.
```

Kernel: `totalCost_le_oneDefectBudget_of_resourcePacking`.

### 5. RFC-facing landing — PASS

For `s-1` cuts, if each cut is crossed by at most one internal demand and

```text
D_i <= 2*(number of selected cuts separating demand i)+2,
```

then the exact `d=2s-1` RL budget follows. The graph/RFC wrapper accepts
literal root-excluding RFC, terminal separation one, and graph cut size at
most two; it derives internal capacity one and applies the arithmetic.

Kernel:

- `totalCost_le_oneDefectBudget_of_articulationCuts`;
- `totalCost_le_oneDefectBudget_of_cutFamily`.

## Single remaining quantified graph lemma

Let `R=(B,M,w,x0)` be a valid one-stub rooted instance with a proper Boolean
bipartition, let `P` be an all-nonbridge `w`-to-`x0` geodesic, and assume

```text
5 <= s,
length(P)=d=2s-1,
|M|>=2,
dist_B(m1(i),m2(i))>=4,
and each demand's endpoints have the same Boolean color.
```

Assume the canonical intervals are in either surviving case classified
above: mass defect or overlap defect. Prove that there exists

```text
cuts : Fin (s-1) -> Finset V
```

such that, for every selected cut `k` and demand `i`,

```text
separationDemand (cuts k) w x0 = 1,
cutSize B (cuts k) <= 2,
dist_B(m1(i),m2(i))
  <= 2 * sum_k separationDemand (cuts k) (m1(i)) (m2(i)) + 2.
```

This is the only unproved node between the classified `d=2s-1` graph
geometry and the kernel-checked RL budget.

## Proposed construction, explicitly unproved

- **Mass defect:** order the disjoint saturated intervals. Select cuts
  immediately before block right endpoints. The unique length-three block
  must contribute the one extra corridor unit in the distance comparison.
- **Overlap defect:** locate the unique unit of interval multiplicity, select
  the ordinary right-end cuts avoiding the over-covered coordinate, and
  duplicate a safe cut if necessary to index the family by `Fin(s-1)`.
- In both cases the intended preliminary comparison is
  `D_i<=2r_i+3`; same-side parity would lower the odd right side to
  `D_i<=2r_i+2`.

None of those three sentences is used as a theorem. In particular, terminal
truncation must be checked separately: it may coincide with the exceptional
long/overlap region, and the proof must show that this does not create a
second lost unit.

## Exact bounded constructor/checker

`one_defect_geometry_verify.py` independently constructs every canonical
mass and overlap geometry for `s=5,6,7,8`:

- every position of the unique length-three mass block;
- all four bipartite-compatible choices of its two optional internal
  attachments;
- every position of the unique overlap between adjacent length-two blocks.

The checked cut construction is sharper than the preliminary description
above. In the mass case it takes the cut immediately before every block
right endpoint, including the terminal block. In the overlap case it takes
all such cuts except the left block's right-end cut at the overlap. That
omitted cut has capacity three; the remaining `s-1` cuts all have capacity
at most two, and no duplicated cut is needed.

For each constructed graph the checker uses exact BFS and finite-set cut
counts. It checks every same-side vertex pair at supply distance at least
four, and then uses an exact 0/1 dynamic program to check every internal-edge
set satisfying the selected-cut capacity constraints. This is a superset of
the RFC-valid internal-edge sets, since RFC and terminal load one permit at
most one internal edge across each selected capacity-two cut.

Reproduction:

```text
$ python3 compute23/gate3/agent_d2s/one_defect_geometry_verify.py
{"cut_feasible_sets_at_least_two": 83000, "geometry_cases": 110,
 "largest_cut_size": 2, "least_pair_margin": 0,
 "least_set_budget_margin": 60, "legal_pairs": 6910,
 "mass_cases": 88, "overlap_cases": 22,
 "s_values": [5, 6, 7, 8], "verdict": "PASS"}
```

It also found every legal pair BFS-level aligned. This independently supports
the BinaryLayers shortcut, but the finite check is only falsification support:
the quantified mass/overlap layer-alignment or cut-construction lemma remains
to be proved in Lean.

## Falsification record

- No volume, vertex-load, shortest-path-routing, or multicommodity theorem is
  asserted, so the `n=8` forced-hub and `n=12` path-packing kills do not apply.
- Mixed demand distances and repeated demands are allowed.
- The arithmetic uses `|M|>=2` explicitly; it is not silently applied to the
  single-demand case.
- Natural subtraction is guarded by `s>=5`; `Fin(s-1)` is nonempty.
- The span-defect contradiction uses an actual proper coloring and actual
  attachment witnesses.
- The equality row `d=2s` is handled in the separate audited module. This
  audit makes no claim about `d<2s-1`.

## Kernel gate

```text
lake env lean ErdosProblems/Erdos23GapGBOneDefect.lean
```

prints only `[propext, Classical.choice, Quot.sound]` or subsets for every
headline theorem. There is no `sorry`, `axiom`, private theorem, floating
point computation, or `native_decide`.
