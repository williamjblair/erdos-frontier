# Hostile audit: the all-nonbridge GB-2SUM counterexample

## Verdict

The proposed graph estimate

```text
D1 + D2 <= n + partnerDistance(d) - 2                 (GB-2SUM)
```

is false even inside the strict bridge-free BF-RL residual.  The explicit
fixture below has

```text
n = 76, d = 11, s = 64, partnerDistance(d) = 1,
(D1,D2) = (38,38),
2*s*partnerDistance(d) = 128 < 144 = (d+1)^2,
D1+D2 = 76 > 75 = n+partnerDistance(d)-2.
```

A selected root--stub geodesic has eleven edges and none is a bridge.
The fixture does **not** disprove RL: its quadratic cost is `3042`, while
its RL budget is `5760`.

Exact reproduction is

```bash
PYTHONPATH=. python3 -u \
  compute23/gate3/agent_weighted_dual/joint_distance_counterexample.py
PYTHONPATH=. pytest -q \
  compute23/gate3/agent_weighted_dual/test_joint_distance_counterexample.py
```

No floating point, random sampling, `native_decide`, or unenumerated finite
claim is used.

## Dependency tree and per-node verdict

```text
GB-2SUM failure
|- A. 11-vertex rooted seed satisfies symmetric RFC       PROVED EXACTLY
|- B. common-endpoint C4 extension preserves RFC          PROVED CUTWISE
|  |- Boolean demand-change inequality                    16/16 rows
|  `- each separating C4 cut has capacity at least two    16/16 rows
|- C. antipodal even-cycle root extension preserves RFC   PROVED CUTWISE
|  |- Boolean separation triangle                         8/8 rows
|  `- attached cycle connects old and new roots           LITERAL C18
|- D. resulting supply is connected and bipartite         VERIFIED/FORMULA
|- E. both demand distances equal 38                      EXACT BFS
|- F. B union M is simple and triangle-free               PROVED/VERIFIED
|- G. selected root geodesic has length 11                EXACT BFS
|- H. every selected root-geodesic edge is nonbridge      11 deletions/BFS
|- I. strict-residual arithmetic                          INTEGER ARITHMETIC
`- J. GB-2SUM fails but RL holds                          INTEGER ARITHMETIC
```

Every node is independent of Conjecture Gamma and RL.  The only imported
mathematical fact is the elementary statement that a path between vertices
on opposite sides of a cut crosses the cut.  For the two gadgets this fact
is expanded into the finite inequalities below.

## A. Exhaustive rooted seed

The seed has vertices `0,...,10`, root `0`, stub `1`, demands

```text
(2,5), (2,6),
```

and supply edges

```text
(0,7),(1,7),(2,7),(0,8),(1,8),(2,8),
(3,9),(4,9),(5,9),(6,9),
(0,10),(1,10),(3,10),(4,10).
```

For every one of its `2^11 = 2048` cuts `T`, the checker directly evaluates

```text
e_B(delta T) - e_M(delta T) - [T separates 0 and 1].
```

All values are nonnegative; the minimum is zero and exactly 24 cuts are
tight.  This is symmetric RFC, hence stronger than checking only cuts that
avoid the root.

The seed distances are `d_B(0,1)=2` and
`d_B(2,5)=d_B(2,6)=6`.

## B. Moving a common demand endpoint through C4 diamonds

Suppose two demands share endpoint `z`, with other endpoints `a,b`.  Attach
a graph `H` at `z`, choose a new vertex `z'` in `H`, and replace the demands
`za,zb` by `z'a,z'b`.  For every cut, write the four side indicators using
the same letters.  The complete Boolean truth table proves

```text
[z' != a] + [z' != b]
  <= [z != a] + [z != b] + 2*[z != z'].             (1)
```

A C4 diamond from `z` to `z'` consists of two internally disjoint
length-two paths.  For every assignment of sides to its four vertices,

```text
2*[z != z'] <= number of crossing diamond edges.     (2)
```

The checker enumerates all 16 rows of (1) and all 16 rows of (2).  Combining
(1), (2), and old RFC proves RFC after one diamond.  Iteration proves it for
a chain of any number of diamonds; there is no asymptotic or uniformity
claim left implicit.

Each diamond adds three vertices and increases the distance from the new
common endpoint to every old-core vertex by exactly two, because the old
endpoint is the unique attachment of the new block to the old graph.

The counterexample uses 16 diamonds.  They add 48 vertices and move the
common endpoint from `2` to `58`, making both demand distances

```text
6 + 2*16 = 38.
```

## C. Moving the root through an even cycle

Attach an even cycle to the old graph at the old root `r`, and choose the
new root `w` antipodal to `r`.  For every cut and every stub-side bit `x`,
the complete eight-row truth table proves

```text
[w != x] <= [r != x] + [w != r].                     (3)
```

If `w` and `r` lie on different sides, each of the two cycle arcs between
them crosses the cut, so the cycle contributes at least two crossing edges;
in particular it contributes at least `[w != r]`.  If they lie on the same
side, the rightmost term of (3) is zero.  Adding (3) to old RFC proves new
RFC for every cut.

The fixture uses a cycle of length 18 and takes its antipodes as `r,w`.
It adds 17 vertices and increases the root--stub distance by nine:

```text
d = 2 + 9 = 11.
```

The selected root geodesic is one nine-edge half-cycle followed by the seed
path `0-7-1`.  Every half-cycle edge lies on C18.  The two seed edges also
lie on cycles, since `0-8-1` is an alternate path.  The checker additionally
deletes each of the eleven edges and performs a full connectivity BFS; all
eleven bridge flags are false.

## D. Order and exact residual arithmetic

For `t` diamonds and a root cycle of length `2k`, the construction has

```text
n = 11 + 3t + (2k-1) = 2k + 10 + 3t,
d = 2 + k,
s = n - 1 - d = k + 7 + 3t,
D1 = D2 = 6 + 2t.
```

At `t=16,k=9`, this gives

```text
n=76, d=11, s=64, D1=D2=38.
```

The residual gates are literal:

```text
n >= 14,                         76 >= 14,
s >= 5,                          64 >= 5,
d <= 2s-2,                       11 <= 126,
2s*p(d) < (d+1)^2,               128 < 144,
|M| = 2,
an all-nonbridge root geodesic exists.
```

The failed bound and the surviving target are

```text
D1+D2 = 76 > 75 = n+p(d)-2,
(D1+1)^2+(D2+1)^2 = 3042 <= 5760 = RL(s,d).
```

Thus replacing GB-2SUM by a differently phrased inequality with the same
linear conclusion would be circular and false.  The two-demand residual
must be aggregated directly at quadratic strength, or with a weaker joint
quantity that admits long shared-endpoint cycle chains.

## E. Legality and triangle audit

The supply is a one-vertex sum of the bipartite seed, sixteen C4 blocks,
and C18.  It is therefore connected and bipartite.  The new common endpoint
is an even distance from the old common endpoint, so each demand remains a
same-colour pair.  Both supply distances are 38, hence at least four.

No triangle can use one demand edge, because its endpoints have supply
distance greater than two.  A triangle using both demand edges would need
the supply edge `5-6`, which is absent.  There are only two demand edges.
Therefore `B union M` is simple and triangle-free.

## F. Adversarial record

This counterexample is not based on any dead route in the standing
falsification record:

- it does not assert volume aggregation;
- it does not assign per-vertex loads;
- it does not sum individual SE1/SE2 bounds;
- it does not invoke multicommodity routing from RFC;
- it is a symbolic infinite-gadget construction with one explicit finite
  instance, not a flag-algebra computation.

It also explains why small exhaustive data did not kill GB-2SUM: the first
failure in this particular all-nonbridge strict-residual family needs a long
root cycle and many capacity-two common-endpoint blocks.  Random sparse
sampling is correspondingly unlikely to hit it.

## Exact remaining gap

After this falsification, the literal `|M|=2` target remains

```text
For every valid one-stub rooted instance in the strict residual with
two internal demands,
  (D1+1)^2 + (D2+1)^2
    <= s*(2d+2+s) + 2s*partnerDistance(d).
```

The counterexample proves that this cannot be obtained from the previously
proposed premise `D1+D2 <= n+p(d)-2`.  It does not establish or refute a
different sufficient aggregation inequality.
