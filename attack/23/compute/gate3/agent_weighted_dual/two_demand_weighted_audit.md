# Hostile audit: weighted two-demand closure for `2d < s`

## Verdict

The production theorem

```text
Erdos23GapGBTwoDemandWeighted.
  totalCost_le_rlBudget_of_twoDemands_twoLength_lt_slack
```

proves the complete `|M|=2` RL inequality whenever

```text
2 * rootStubDistance < slack.
```

The companion headline

```text
Erdos23GapGBTwoDemandWeighted.
  totalCost_le_rlBudget_of_twoDemands_twoLength_le_slack_of_even
```

also includes the closed boundary `2d=s` whenever `d` is even.
The third graph headline

```text
Erdos23GapGBTwoDemandWeighted.
  totalCost_le_rlBudget_of_twoDemands_even_near_twiceLength
```

closes the first three rows below that boundary:
`2d-3<=s<=2d`, for positive even `d>=6`.

It does not use the false order-only estimate
`D1+D2 <= n+partnerDistance(d)-2`.  Instead it derives and combines the two
weighted inequalities

```text
2*Dmax <= 2s+d,                    rooted SE2
Dmin+2*Dmax <= 2(s+d).             internal-pair SE2
```

The theorem is graph-level, unconditional in this ratio, and kernel checked
with exactly `[propext, Classical.choice, Quot.sound]`.

## Dependency tree and per-node verdict

```text
two-demand RL for 2d<s
|- A. RFC => internal two-demand cut condition            KERNEL PROVED
|- B. G-A on the two internal geodesics                   ALREADY PROVED
|  `- Dmin+2*Dmax <= 2(card(V)-1)=2(s+d)                 KERNEL PROVED
|- C. RFC => rooted SE2 for the larger demand             ALREADY PROVED
|  `- 2*Dmax <= 2s+d
|- D. weighted convex interval arithmetic                 KERNEL PROVED
|  |- equal-distance endpoint                             KERNEL PROVED
|  `- rooted-SE2 endpoint                                 KERNEL PROVED
`- E. Fin 2 sum/index dispatch                            KERNEL PROVED
```

No node assumes a multicommodity routing, path packing, vertex-load bound,
joint distance sum, induction hypothesis, or theorem of RL strength.

## A. Exact graph derivation

Symmetric RFC says, for every cut `T`,

```text
sum_{i:Fin 2} separation(T,mi1,mi2) + separation(T,w,x0)
  <= cutSize(B,T).
```

Dropping the nonnegative rooted term gives the literal G-A two-demand cut
condition for the two internal demand pairs.  Apply the proved symmetric
G-A ledger to geodesics of lengths `D0,D1`.  In the orientation with the
smaller distance first, its SE2 conclusion is

```text
2*Dmax <= 2*(card(V)-1-Dmin)+Dmin,
```

which is exactly

```text
Dmin+2*Dmax <= 2*(card(V)-1)=2(s+d).
```

Independently, applying the existing rooted SE2 theorem to the larger
internal demand gives `2*Dmax<=2s+d`.  The Lean proof constructs both
internal geodesics from connectedness, derives both orientations, and then
dispatches on the actual order of `D0,D1`.

## B. Exact arithmetic landing

Put

```text
a=Dmin+1, b=Dmax+1,
L=2s+2d+3, U=2s+d+2,
R=s^2+2sd+4s.
```

The two graph inequalities become

```text
a+2b<=L, 2b<=U, a<=b.
```

The feasible interval has two convex endpoints.

1. At the equal endpoint, `3b<=L`, so
   `9(a^2+b^2)<=2L^2`.
2. At the rooted endpoint, `2b=U` and
   `a=L-U=d+1`, so
   `4(a^2+b^2)<=4(d+1)^2+U^2`.

For the middle interval the proof introduces exact natural slacks

```text
c+2b=L, c+q=b, 2b+r=U, r+d+1=c.
```

The factorization deciding which endpoint dominates is explicit:

```text
2L^2 - 9(c^2+b^2) = q*(6b-7q),
[4(d+1)^2+U^2] - 4(c^2+b^2)
  = r*(4b+5r-8c).
```

The case split `5(2q+3r)<=4L` proves the first factor nonnegative;
its complement proves the second factor nonnegative.  These identities and
all truncated-natural side conditions are kernel checked.

Write `s=2d+1+t`, possible because `2d<s`.  The two endpoint budget gaps
reduce to

```text
9R-2L^2
  = 6dt+6d+t^2+14t-5 >= 0,
4R-[4(d+1)^2+U^2]
  = 3d^2+4dt+8d+8t >= 0.
```

The theorem assumes `d>=1`, so the first right side is at least one.  Finally
`partnerDistance(d)>=1` gives

```text
R <= s(2d+2+s)+2s*partnerDistance(d).
```

No unquantified approximation occurs.

For positive even `d`, `partnerDistance(d)=2`.  Repeating the same convex
interval calculation with `s=2d+t` and this extra partner unit gives endpoint
gaps

```text
9R-2L^2 = 6dt+36d+t^2+30t-18 >= 0,
4R-[4(d+1)^2+U^2]
  = 3d^2+4dt+20d+16t-8 >= 0.
```

Both are positive already at `d=1,t=0`.  This proves the second headline
throughout `2d<=s` for even root distance, including the previously missing
equality boundary.

For the first three rows below the boundary, put `r=2d-s`, so
`r` is one of `0,1,2,3`.  With partner two the endpoint gaps are

```text
9R-2L^2 = -6dr+36d+r^2-30r-18,
4R-[4(d+1)^2+U^2]
  = 3d^2-4dr+20d-16r-8.
```

Literal four-way interval dispatch and `d>=6` make both nonnegative.  This
is the arithmetic core of the third graph headline.

## C. Exact reproduction

Direct kernel check:

```bash
lake env lean ErdosProblems/Erdos23GapGBTwoDemandWeighted.lean
```

Expected axiom report for all eight exported theorems:

```text
[propext, Classical.choice, Quot.sound]
```

Hostile arithmetic and fixture tests:

```bash
PYTHONPATH=. pytest -q \
  compute23/gate3/agent_weighted_dual/test_two_demand_weighted.py
```

The arithmetic test checks all `2,702,789` integer tuples in

```text
1<=s,d<=80, 2d<s, 0<=Dmin<=Dmax,
2Dmax<=2s+d, Dmin+2Dmax<=2(s+d).
```

It performs ordinary integer arithmetic and obtains zero failures.
The partner-two test checks another `2,765,969` tuples with `2d<=s`, of
which `63,180` lie exactly on `2d=s`; it also obtains zero failures.
The near-boundary partner-two test checks `1,909,006` further tuples on
`2d-s in {0,1,2,3}`, again with zero failures.

## D. Mandatory hostile fixtures

- **New all-nonbridge n=76 GB-2SUM kill.**  It lies inside the theorem:
  `d=11,s=64`, hence `22<64`; `Dmin=Dmax=38`;
  `76<=139` and `114<=150` are the two weighted premises.  Its false
  order-only premise is not used.  The headline proves the observed
  `3042<=5760` RL inequality.
- **n=8 forced hub (`G?`F`w`, cut 15).**  Exact decoding gives two
  distance-four demands but zero valid nontrivial rooted stub pairs.  No
  vertex-load premise occurs.
- **n=12 path-packing witness (`K??E@_qi?]Ia`, cut 63).**  Exact decoding
  gives four demands and zero valid rooted stub pairs.  It is outside the
  `Fin 2` theorem, and no volume or routing claim occurs.
- **mixed-distance Holder witness (`H?AFBo]`, cut 31).**  Exact decoding
  gives distances `(4,6)` and zero valid rooted stub pairs.  Again no Holder
  or volume inequality is used.
- **balanced odd-cycle blow-ups.**  The proof uses only RFC consequences
  already proved by G-A.  It introduces no stability or strictness claim
  about the equality family.  The `2d<s` result is compatible with every
  member that happens to meet its literal two-demand hypotheses.
- **thin corridors.**  The new ratio is the opposite regime: `2d<s`.
  The banked `s=2,3` thin-corridor records therefore cannot satisfy it for
  positive `d`.

The pytest reproduces the first three named graph6 checks exactly, including
the zero-root counts.

## E. Exact remaining gap

For `|M|=2`, these theorems remove every rooted instance with `2d<s`, and
for even root distance they also remove the first three rows down through
`s=2d-3`.  The remaining quantified slice is

```text
connected bipartite B, two legal internal demands, RFC,
n>=14, s>=5, d>=3,
((d is even and s<=2d-4) or (d is odd and s<=2d)),
2s*partnerDistance(d)<(d+1)^2,
and the previously banked bridge/boundary reductions,

prove
(D1+1)^2+(D2+1)^2
  <= s(2d+2+s)+2s*partnerDistance(d).
```

This is strictly smaller than the prior two-demand frontier and is not a
restatement of RL: the entire `2d<s` region and four even-root boundary rows
are now closed by two independently proved linear consequences of RFC.
