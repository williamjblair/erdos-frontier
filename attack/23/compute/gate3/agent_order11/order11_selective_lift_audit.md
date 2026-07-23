# Hostile audit: selective order-11 consistency for Erdős #23

## Verdict

The exact order-11 deletion separator is valid; the first two rooted-profile
reconstructions were not.  The corrected status is:

1. The frozen positive-delta order-10 Horn optimizer is **not** an order-11
   vertex-deletion marginal.  A set `S` of 1,439 order-10 types has

   ```text
   q(S) = 0.5500954641343327... > 6/11,
   ```

   while every order-11 type has at most six of its eleven deletions in `S`.
   This is an exact integer separator.
2. A separator for one floating optimizer does not close the re-optimized
   relaxation.  The shipped archive also omits the historical 6,359-row
   envelope/Horn coefficient cache.
3. Choosing one raw canonical-coordinate profile for an unlabeled graph type
   is **not relabel-invariant**.  Explicit order-9 and order-10 witnesses are
   frozen below.  Every LP run using those raw coefficients is invalid and is
   excluded from the conclusions.
4. Two sound repairs were rebuilt:

   - profile colourings constant on one-extension isomorphism orbits;
   - arbitrary raw-coordinate colourings averaged over the full
     automorphism group `Aut(R)`.

   Both have exact coefficientwise all-one identities.  The Aut-averaged
   construction also passes the frozen relabel witnesses and 40 additional
   random relabelings exactly.  A separate durable run exhausts every
   relabeling of one deterministic fixture at each order 4 through 8.
5. On the balanced `C5` blow-up, exact evaluation of the chosen colourings
   gives:

   ```text
   orbit k7 = 2/25,        orbit k8 = 2/25 + 168/78125,
   Aut-averaged k7 = 2/25, Aut-averaged k8 = 2/25.
   ```

   Thus the orbit `k7` leg is sharp enough for the true boundary example,
   while Aut averaging repairs the `k8` leakage.  These are boundary checks,
   not global closure results.

No exact rational dual or full Erdős #23 proof is claimed here.

## Dependency tree and per-node verdict

```text
Frozen optimizer is not order-11 extendable
|- A. enumerate T10/T11 triangle-free types with geng          EXACT COUNTS
|- B. canonize all 11*105071 deletions with labelg             REBUILT
|- C. integer deletion matrix C=11*D11                         EXACT
|  |- shape 12172 x 105071, nnz 979924                        VERIFIED
|  `- every column sum is 11                                  VERIFIED ALL
|- D. fixed S has 1439 rows                                   HASHED MANIFEST
|- E. max column mass on S is 6                               VERIFIED ALL
`- F. frozen-q violation                                      EXACT FRACTIONS

Raw-profile route
|- G. n=9 relabel witness: 8/30 versus 6/30                   EXACT
|- H. n=10 relabel witness: 10/24 versus 12/24                EXACT
`- I. raw unlabeled coefficients are invalid                  FALSIFIED

Sound profile repairs
|- J. orbit k7/k8 coloured-extension canonization              INVARIANT
|  |- all-one identities e(H)/36 and e(H)/45                  VERIFIED ALL
|  `- cache digests 54b2... and 6649...                       REPRODUCED
|- K. Aut-averaged k7/k8                                      INVARIANT
|  |- average every profile pair over Aut(R)                  INTEGER COUNTS
|  |- all-one identities e(H)/36 and e(H)/45                  VERIFIED ALL
|  |- raw witnesses become exactly equal                      VERIFIED
|  |- 40 further random relabelings                           VERIFIED
|  `- exhaustive fixture relabelings through n=8              VERIFIED
`- L. balanced-C5 chosen landings                             EXACT FRACTIONS
```

No node invokes Erdős #23, RL, Gamma, `native_decide`, graphon compactness,
or an unquantified asymptotic statement.

## Exact D11 reconstruction

`order11_k8_lift.py build-d11` runs `geng -q -t 10`,
`geng -q -t 11`, and `labelg -q -g`, then canonizes every deletion.  A fresh
rebuild and the inherited parent cache have the same integer-triple digest:

```text
shape                 12172 x 105071
nonzero entries       979924
integer entry range   1,...,11
every column sum      11
SHA256                 75eef4c5895491ad95d6138297cf594be424cdabfaaa85692392fb022d77b53e
```

Floating cache entries are accepted only after checking that each is the
stored float representation of an integer divided by eleven.  Certificate
comparisons use the integers.

## Exact binary separator

`S` is embedded as a bitset in `check_binary_separator.py`.  The sorted index
list has SHA256

```text
b95a542c016ccfa9ded23ae4728e061dbcac9b9cda91a6dd35fbc7f039b3e04d.
```

`order11_binary_separator_manifest.json` records all 1,439 indices and both
enumeration and canonical graph6 strings; its file SHA256 is

```text
fd673f8567975d4e9a984f9e7a6d7d71b574b008c0fcaa0bbc1d87ba88a7c082.
```

The number of selected deletions over all 105,071 T11 columns has histogram

```text
selected count        0      1      2      3     4     5    6
number of columns  35708  30016  21285  10714  5343  1738  267
```

and is never seven.  Therefore every probability vector `r` satisfies

```text
(D11*r)(S) <= 6/11.
```

For the stored `horn_dual.pkl` primal vector, negative roundoff is clipped to
zero, every remaining binary float is converted with `Fraction.from_float`,
and normalization is exact.  The positive cross-multiplied gap is

```text
32356848425285966149385090973 /
633825300114114700748351602688 > 0.
```

This exact claim concerns the diagnostic primal vector as stored; the vector
is not itself a theorem certificate.

## Frozen relabel counterexamples to raw canonical profiles

The deterministic colour of a raw profile is the low bit of

```text
SHA256(bytes(root_key) || 0xff || bytes(profile)).
```

`profile_relabel_invariance.py` reproduces:

```text
n=9:  graph6 H?Bedrw
      new-to-old permutation [0,2,5,7,4,8,3,1,6]
      raw same-colour ordered-edge counts 8/30 versus 6/30.

n=10: graph6 I??E@bG}?
      new-to-old permutation [3,7,9,8,4,6,5,2,0,1]
      raw same-colour ordered-edge counts 10/24 versus 12/24.
```

Thus one arbitrary canonical tie-breaking does not define a coefficient on
an unlabeled density vector.  Canonicalizing the full one-vertex extension
instead collapses automorphic profiles and is invariant, but restricts the
available rules.  Averaging the raw rule over `Aut(R)` retains the rule while
removing the tie.

All earlier raw-coordinate master runs are invalidated.  In particular,
their objective values must not be used positively or negatively.

## Sound cache manifests

The orbit-invariant caches use `labelg` with a distinguished extension
partition.  Their exact manifests are

```text
k7 orbit: T9 -> 107 roots, 20432 entries, profile counts 5..36,
  SHA256 54b2f3a1e4961063887427ae1521f3e1d8db1e36fe4da2a8c5efde7703aedf6d.

k8 orbit: T10 -> 410 roots, 160238 entries, profile counts 5..72,
  SHA256 6649fe11145b113390fd6cc69740d5aaa03b6b5c707dee3333ac4b12d7e48dce.
```

For Aut averaging, each edge/root occurrence is expanded by every
automorphism, then identical profile pairs are aggregated.  The coefficient
of one aggregate is

```text
count / (C(n,2) * |Aut(R)|).
```

The manifests are

```text
k7 Aut: 34182 aggregates, 477621 expanded occurrences,
  |Aut|=1..5040, profiles 23..128,
  SHA256 5e3567a369a293c288a507ba1aabe57e845e28cf4a20b7a39a19dca52807d4cd.

k8 Aut: 276334 aggregates, 4612843 expanded occurrences,
  |Aut|=1..40320, profiles 31..256,
  SHA256 8de920c0e9204f1faad49008b6b47100e561000ef40628d703fd197b05c5fd63.
```

For every one of the 1,897 T9 states and 12,172 T10 states, summing the
all-one coefficients gives exactly `e(H)/36` and `e(H)/45`, respectively.
On both frozen raw-profile witnesses the Aut-averaged coefficient vector is
unchanged by the stated permutation; 400 additional random relabelings pass
the same exact `Fraction` comparison.  The durable result file additionally
exhausts all relabelings of deterministic fixtures at orders 4 through 8:
24, 120, 720, 5,040, and 40,320 permutations, respectively.

## Balanced-C5 boundary

`balanced_c5_sound_envelopes.py` constructs the exact T9/T10 density of the
balanced five-part blow-up using multinomial integer weights.  A floating
local MaxCut search chooses a colouring, after which the landing is evaluated
with integers and `Fraction` arithmetic.  Optimality of the MaxCut search is
not needed: any explicit colouring is a valid upper-envelope row.

The exact chosen landings are

```text
orbit k7          2/25,
orbit k8          6418/78125 = 2/25 + 168/78125,
Aut-averaged k7   2/25,
Aut-averaged k8   2/25.
```

The true balanced-`C5` bipartization density is `2/25`, so each landing at
`2/25` is boundary-tight.  The orbit `k8` excess is a limitation of that
restricted leg only; it is removed either by taking the minimum with orbit
`k7` or by using the stronger Aut-averaged `k8` leg.

## Incomplete sound master diagnostics

Two sound column-generation diagnostics were stopped when the campaign goal
changed.  Neither is a closure result or counterexample.  With D11, the 87
shipped Gram-atom rows, and orbit-invariant profile rows, the completed
master objective values were:

```text
k7 only, iterations 0..3:
  0.23970000000000005
  0.14638252401459867
  0.08734115930401805
  0.058022333682915976

k7+k8, iterations 0..2:
  0.23970000000000005
  0.13392956145221105
  0.08399079578064401
```

Both still had a violating pricing row when stopped.  The exact stdout event
records are frozen in `k7_only_master_partial.jsonl` and
`orbit_master_partial.jsonl`.  In the final recorded k7-only event the
floating pricing violation was `worst7 = 0.0027012630855764155`.  In the
final recorded k7+k8 event they were
`worst7 = 0.004238247603719647` and
`worst8 = 0.004570049210376813`.  These are diagnostics, not exact rational
bounds.  The runs predate the checkpoint patch and therefore have no
resumable state file.  `order11_combined_master.py` now contains
checkpoint/resume and optional dynamically separated moment rows, but those
later code paths have only received syntax and command-line smoke checks,
not an expensive end-to-end run.

## Reproduction

```bash
PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/order11_k8_lift.py \
  build-d11 /tmp/erdos23_d11.npz

PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/check_binary_separator.py \
  /tmp/erdos23_d11.npz

PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/order11_k8_lift.py \
  build-k7-orbit /tmp/erdos23_k7_orbit.npz
PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/order11_k8_lift.py \
  build-k8-orbit /tmp/erdos23_k8_orbit.npz

PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/order11_k8_lift.py \
  build-k7-aut /tmp/erdos23_k7_aut.npz
PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/order11_k8_lift.py \
  build-k8-aut /tmp/erdos23_k8_aut.npz

PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/profile_relabel_invariance.py \
  --random-trials 20 --exhaustive-through 8

PYTHONDONTWRITEBYTECODE=1 python \
  compute23/gate3/agent_order11/balanced_c5_sound_envelopes.py \
  /tmp/erdos23_k7_orbit.npz /tmp/erdos23_k8_orbit.npz \
  /tmp/erdos23_k7_aut.npz /tmp/erdos23_k8_aut.npz
```

## Falsification record

- One D11 separator is not promoted to a re-optimized bound.
- Raw canonical-coordinate rows are rejected by exact relabel witnesses.
- The invalid raw masters are excluded from all conclusions.
- Orbit invariance and Aut averaging are kept distinct.
- The orbit `k8` balanced-`C5` excess is not attributed to Aut `k8`.
- Floating colour search is followed by exact rational landing evaluation.
- The unavailable historical cut cache is not silently assumed.
- No incomplete cutting-plane pool is called a full envelope.

## Exact remaining gap

The sound finite-lift target isolated here is:

```text
For every probability distribution r on the 105071 triangle-free T11 types,
set q10=D11*r and q9=D10*q10.  Impose the closed edge-density band, a fully
specified finite pool of relabel-invariant k7/k8 profile rows (orbit or
Aut-averaged), and exact moment/Horn positivity rows.  Prove that the maximum
deficit eta is <= 0.
```

Progress requires an exact rational dual of such a fully specified sound LP,
or a theorem subsuming it.  The binary separator is a valid new row but does
not alone prove this quantified lemma.
