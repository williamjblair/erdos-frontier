# Hostile audit: pure-mass cut coordinates

Status: **the cut-family landing is kernel checked; structural existence is
conditional; the original `sum D <= d` pure-mass claim is false.**

## 1. Audited dependency tree

### A. Arithmetic landing from `sum D <= 2s`

For at least two legal distances `D_i >= 4`, the bound

```text
sum_i D_i <= 2s,   3s <= 2d
```

implies the exact RL budget.  Verdict: **kernel checked** as
`totalCost_le_rlBudget_of_sumDistances_le_twiceSlack` in
`Erdos23GapGBIsometricCuts.lean`.

### B. RFC landing from a repeated cut family

Suppose a finite family of cuts, with repetitions allowed, satisfies:

```text
card K <= 2s;
every cut separates w from x0;
every cut has B-cut size at most two; and
dist_B(m1(i),m2(i)) <= number of family cuts separating demand i.
```

RFC leaves aggregate internal-demand capacity at most one in each column.
Summing gives `sum_i D_i <= card K <= 2s`, and node A closes RL.

Verdict: **kernel checked** as
`totalCost_le_rlBudget_of_dominatingTwoCutFamily_twiceSlack`.  The theorem
does not assert that a pure-mass graph has such a family.

### C. Literal Theta/isometric basis

Claim challenged: disjoint saturated pure-mass blocks always form a chain of
even cycles with `d` size-two Djokovic/Theta coordinates.

Verdict: **false**.  A size-two span-three block with its first optional
attachment has a size-three Djokovic class.  With both optional attachments,
the Djokovic relation is not transitive.  The complete constructor scan
through `s=10` has 1,800 instances without the literal size-two Theta basis
and 840 non-partial-cubes among 1,920 constructors.

### D. The stronger distance sum `sum D <= d`

Verdict: **false**, even under exact RFC.  The first witness has

```text
s=6, d=10,
blocks q1 -- q2(option 1) -- q2(option 1) -- q1,
M = {(0,13), (3,15), (6,10)},
distances = (4,4,4).
```

Thus `sum D=12>d=10`.  Its supply edges are

```text
(0,1) (0,11) (1,2) (2,3) (2,11) (2,12)
(3,4) (3,13) (4,5) (5,6) (5,13) (5,14)
(6,7) (6,15) (7,8) (8,9) (8,15) (8,16)
(9,10) (10,16) (12,13) (14,15).
```

All `2^17` cuts are checked with integer cut vectors.  The rooted terminal is
`(0,10)`.  The three-demand family satisfies RFC exactly.  Its quadratic
cost is `75`, far below `rlBudget(6,10)=192`; the witness kills the proposed
linear strengthening, not RL.

### E. Two-defect correction `sum D <= d+2 = 2s`

Every complete pure-mass constructor through `s=10` admits a repeated
terminal-separating size-two cut family of total weight `d+2=2s` dominating
every legal same-side distance.  Exact counts:

```text
constructors                          1920
q3 constructors                       576
q2+q2 constructors                   1344
d-coordinate certificates            1605
d-coordinate failures                 315
failures repaired at d+2              315
d+2 failures                             0
```

All 576 size-three-block constructors already have a `d`-coordinate
certificate; every one of the 315 failures occurs in the two-size-two-block
shape.

Verdict: **bounded exact evidence, not a theorem**.  The cut enumerator is
complete: every cut of capacity at most two is obtained by removing zero,
one, or two supply edges and taking all eligible unions of the resulting
components.  This enumeration was independently compared with all vertex
subsets on every constructor through `s=4`.

The exact remaining structural lemma for this route is:

```text
For every pure-mass canonical graph at d=2s-2, there is a multiset K of
at most 2s root--stub-separating B-cuts, each of cut size at most two, such
that every legal same-side pair uv is separated by at least dist_B(u,v)
members of K.
```

No Lean theorem or paper proof currently supplies this existence claim.

## 2. Size-three exceptional block audit

For a saturated size-three span-four block beginning at `l`, the three
unaligned local candidate types are

```text
A = (p[l+1], cR),
B = (p[l+2], cM),
C = (p[l+3], cL).
```

The four optional attachment bits are, in order,

```text
cM--p[l+1], cL--p[l+2], cR--p[l+2], cM--p[l+3].
```

Exact legality is:

```text
A legal iff bits 0 and 2 are absent;
B legal iff all four bits are absent;
C legal iff bits 1 and 3 are absent.
```

Hence any two legal types force the chordless block.  In that case the
complement of `corridorLeftRegion P l` has cut size two, separates the rooted
terminals, and separates all three types.  RFC therefore permits at most one
candidate type.

`probe_q3_unaligned_candidates.py` checks all 240 q3 constructors through
`s=7`: 135 have no legal candidate, 90 have one, and 15 have all three.
Those 15 are exactly the chordless cases, and the displayed residual cut
kills all 45 candidate pairs.  There are no failures.

## 3. Reproduction

```text
python3 -m compute23.gate3.agent_aggregation.probe_pure_mass_isometric \
  --max-s 10 --skip-corpus --skip-rfc-optimisation --skip-rfc-witness

python3 -m compute23.gate3.agent_aggregation.probe_pure_mass_isometric \
  --max-s 6 --skip-corpus --skip-rfc-optimisation

python3 -m compute23.gate3.agent_aggregation.probe_q3_unaligned_candidates \
  --max-s 7

lake env lean ErdosProblems/Erdos23GapGBIsometricCuts.lean
```

The first command reproduces the 1,920-constructor cut-family census.  The
second independently emits the exact RFC counterexample to `sum D<=d`.
The third reproduces the size-three candidate classification and residual
cut.  The direct Lean check reports only
`[propext, Classical.choice, Quot.sound]` for the generic twice-slack RFC
landing.

## 4. Circularity and boundary check

- Repeated cuts are literal repetitions in the finite index type; no false
  assertion that Djokovic classes remain size two is used.
- The false `sum D<=d` statement is retained with its exact witness.
- The surviving `2s` certificate existence is not advertised as proved.
- The finite constructor census is not substituted for the all-`s` graph
  lemma.
- The graph-independent Lean theorem assumes only its displayed cut family
  and does not assume RL or a same-order Gamma bound.
