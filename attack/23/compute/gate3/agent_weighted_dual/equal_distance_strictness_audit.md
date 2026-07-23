# Equal-distance strictness audit

## Exact target and scope

For two distinct internal demands of a connected finite supply graph, write
their common even supply distance as `D` and the supply order as `n`.  The
strict order estimate isolated here is

```text
3 D <= 2 (n - 2).
```

The current kernel theorem
`three_mul_equalLength_le_card_sub_two_of_allNonbridge` proves this when a
geodesic for the first demand is all-nonbridge.  The proof does not claim the
stronger false estimate `3 D <= 2 (n - 3)` and does not claim a full
two-demand RL closure.

## Dependency tree

```text
two-demand cut condition
  -> G-A weighted bound 3D <= 2(n-1)                  KERNEL PROVED
  -> equality gives D = 2*slack(P)                   KERNEL PROVED
  -> all-nonbridge double-slack rigidity              KERNEL PROVED
     -> every vertex has left/next even anchors       KERNEL PROVED
     -> only P's terminals are distance 2*slack(P)    KERNEL PROVED
  -> distinct demand pairs rule out equality          KERNEL PROVED

bridge dispatch
  -> bridge cut keeps second geodesic on one side     KERNEL PROVED
  -> canonical bridge side is induced-connected       KERNEL PROVED
  -> bridge-side cut extension preserves capacity     KERNEL PROVED
  -> induced two-demand cut condition                  KERNEL PROVED
  -> contained geodesics remain induced-geodesic       KERNEL PROVED
  -> localize prefix/suffix and apply induced SE2       REMAINING
```

Every use of "unique diameter" is quantified literally: if `slack(P) >= 2`
and `dist(x,y)=length(P)=2*slack(P)`, then the unordered pair `{x,y}` is the
unordered pair of endpoints of `P`.

## Tight hostile fixture

The eight-vertex supply has edges

```text
(0,5) (1,5) (0,6) (2,6) (3,6) (1,7) (2,7) (4,7)
```

and demands `(0,4)` and `(1,3)`.  Exact enumeration of all `2^8` cuts gives
nonnegative cut slack, both demand distances are four, and

```text
3D = 12 = 2(n-2) > 2(n-3) = 10.
```

Thus the proved constant is sharp.  Exact enumeration of every simple path
for both pairs also finds no edge-disjoint routing pair.  Consequently the
two-commodity cut condition cannot be replaced by an asserted
edge-disjoint-routing theorem.  Both facts are reproduced by
`test_equal_distance_odd_spindle.py`.

## Arithmetic landing and surviving rows

Combining only the equal-distance strictness with the already-proved rooted
SE2 and internal weighted bounds closes the uniform rows
`r = 2d-s <= 3` for both root parities.  With partner distance two it closes
the even-root rows through `r <= 6`.  It does not close the full band
`s < 2d`.

The first surviving unequal arithmetic witnesses are exact:

```text
odd root:  (s,d,x,y) = (10,7,10,12), deficit 10, r=4;
even root: (s,d,x,y) = ( 9,8,10,12), deficit 11, r=7.
```

They satisfy the existing root SE2 and internal weighted inequalities.
Removing them requires a genuinely stronger unequal-distance graph bound;
equal-distance strictness alone cannot do so.
