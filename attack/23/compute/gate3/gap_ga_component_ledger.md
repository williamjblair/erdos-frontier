# Candidate proof of gap G-A by component spans

Status: **PROVED on paper; second hostile audit PASS.**  The first hostile
audit found and repaired one false exceptional-component subclaim.  The
revised proof passed a second node-by-node audit and exact structural
enumeration; see `gap_ga_audit.md`.  The Lean module now checks the bridge,
metric, canonical-component, exact `q_C/r_C`, attachment-span,
ridden-owner, and local-charge layers.  The remaining intake step is
exactly `CanonicalChargeTheorem`: construct the simultaneous canonical
ride/excursion assignment with interval packing and exceptional-tail
dispatch.

## Symmetric two-demand lemma

Let `B` be a finite connected simple graph on `n` vertices.  Fix terminal
pairs `(w,x0)` and `(y,z)` and suppose that every vertex cut `T` satisfies

```text
[# T separates w,x0] + [# T separates y,z] <= e_B(delta T).       (C)
```

Let `P = u_0 ... u_d` be a `w`--`x0` geodesic, and let `Q` be a
`y`--`z` geodesic of length `D`.  Put `s = n-1-d`.  Then

```text
D <= 2s.                                                           (S)
```

The same lemma with the demand pairs interchanged gives

```text
d <= 2(n-1-D),
```

and hence `2D <= 2s+d`.

For a valid rooted one-stub instance with `|M|=1`, condition (C) is exactly
the symmetric rooted flip condition `RFC†`.  Therefore (S) is SE1, its
swapped version is SE2, and the already-proved `SE1 and SE2 => RL` theorem
closes the requested single-edge gap G-A.

## Proof of the symmetric lemma

If `Q` is disjoint from `P`, all `D+1` of its vertices lie off `P`, so
`D+1<=s` and the conclusion is immediate.  If `Q` meets `P` in exactly one
vertex, its other `D` vertices lie off `P`, so `D<=s`.  We may therefore
assume at least two common vertices.

Orient `Q` so that its visits to `P` occur in increasing corridor order.
This is possible: a subpath of a geodesic is geodesic, so between the first
and last visits the sum of the absolute changes in corridor position equals
the absolute total change.  Equality in the triangle inequality forces all
changes to have the same sign.

Delete the vertices of `P` from `B`, and let `C` range over the connected
components of the remaining graph.  For each component define

```text
A_C = {j : some vertex of C is adjacent to u_j},
l_C = min A_C,
h_C = max A_C,
I_C = the h_C-l_C corridor edges from u_l_C to u_h_C,
t_C = |C|.
```

Every `A_C` is nonempty by connectedness.  Moreover

```text
|I_C| = h_C-l_C <= t_C+1.                                         (1)
```

Indeed, choose vertices of `C` adjacent to the two extreme attachments.
A simple path between them inside the connected `t_C`-vertex component has
at most `t_C-1` edges; adding the two attachment edges gives a walk of
length at most `t_C+1` between `u_l_C` and `u_h_C`.  Since `P` is geodesic,
its subpath has minimum possible length `h_C-l_C`, proving (1).  The same
argument covers coincident attachment vertices.

Call a corridor edge *ridden* if it belongs to both `P` and `Q`, and let `R`
be the set of ridden edges.  Every ridden edge lies in at least one interval
`I_C`.  Otherwise it is a bridge of `B`: an alternate path around that
corridor edge must leave `P` in a component attached on one side and return
on the other, which would put the edge in that component's attachment
interval.  But a ridden bridge separates both terminal pairs, contradicting
(C), whose left side is two while the bridge cut has capacity one.

Assign each ridden edge to one component whose interval contains it.  Write
`R_C` for the ridden edges assigned to `C`.

Between consecutive visits of `Q` to `P`, either `Q` rides a corridor edge
or it makes an *excursion*: a subpath whose internal vertices lie in one
component `C`.  If the attachment positions differ by `g`, the excursion
also has length `g`, because both it and the corresponding `P` subpath are
geodesics.  It therefore has `g-1` vertices off `P`.  Excursion gap intervals
are pairwise edge-disjoint, and none contains a ridden edge.

For each component let

```text
E_C     = number of Q-excursions through C,
G_C     = sum of their corridor-gap lengths,
qexc_C  = number of their internal vertices = G_C-E_C,
q_C     = |C intersect V(Q)|,
r_C     = |C setminus V(Q)|.
```

The assigned ridden edges and the excursion gap intervals are disjoint
subsets of `I_C`; hence, using (1),

```text
|R_C| + G_C <= |I_C| <= q_C+r_C+1.                                (2)
```

If `qexc_C+r_C >= 1`, then (2) gives

```text
|R_C|+E_C
  <= q_C+r_C+1-G_C+E_C
   = q_C+r_C+1-qexc_C
  <= q_C+2r_C.                                                     (3)
```

It remains to handle the only exceptional case
`qexc_C=r_C=0`.  Then every vertex of `C` lies on `Q`, and `C` contains no
excursion.  Thus its `Q`-vertices can occur only in the initial off-`P`
tail, the final off-`P` tail, or both.

They cannot occur in both.  If they did, both `y` and `z` would lie in `C`.
Connectedness would give a `y`--`z` path inside `C` of length at most
`|C|-1=q_C-1`, while `Q` contains all `q_C` vertices of `C` and at least
one vertex of `P`, so its length is at least `q_C`.  This contradicts that
`Q` is geodesic.

Suppose therefore that `C` is the initial-tail component.  Let `u_a` and
`u_c` be the first and last visits of `Q` to `P`.  The initial tail has
length `alpha=q_C=|C|`.  Although `C` may have unused forward attachments
(the first hostile audit found exact valid examples), it still satisfies

```text
|R intersect I_C| <= min(c,h_C)-a <= q_C.                           (4)
```

Only the second inequality needs proof.  If it failed, integrality would
give `h_C-a>=q_C+1` and `c>=h_C`.  Since `u_a` is an attachment and (1)
gives `h_C-l_C<=q_C+1`, necessarily

```text
l_C=a,  h_C-a=q_C+1.
```

Choose a vertex of `C` attached to `u_h_C`.  A simple path inside the
connected `q_C`-vertex component from `y` to that vertex, followed by its
attachment edge and then `P[u_h_C,u_c]`, has length at most

```text
q_C + c-h_C < q_C + c-a.
```

But the `y`--`u_c` subpath of `Q` is geodesic and has length exactly
`q_C+c-a`: the initial tail contributes `q_C`, and the segment between
the two corridor visits has length `c-a`.  This contradiction proves (4).
The final-tail case is symmetric.  Thus for every assignment
`|R_C|<=q_C`, which is exactly inequality (3) when
`qexc_C=r_C=E_C=0`.

Summing (3) over all components yields the missing ledger

```text
|R| + E <= sum_C (q_C+2r_C) = q+2r,                               (L)
```

where `E=sum E_C`, `q=|V(Q) setminus V(P)|`, and
`r=|V(B) setminus (V(P) union V(Q))|`.

Finally, if the initial and final off-corridor tails have total length
`alpha+beta` and the excursion gaps have total length `G`, then

```text
D = alpha+beta+G+|R|,
q = alpha+beta+(G-E).
```

Using (L),

```text
D = q+E+|R| <= 2q+2r = 2(n-1-d) = 2s,
```

which proves the symmetric lemma.

## Audit obligations

1. Recheck the explicit zero/one-intersection dispatch and monotonicity when
   `P` and `Q` share isolated vertices or whole subpaths.
2. Verify the bridge/attachment-interval equivalence without assuming that
   an alternate path leaves and returns to `P` only once.
3. Check that an excursion's off-`P` vertices all lie in one component and
   that all excursion gap intervals are disjoint from the ridden set.
4. Attack the revised exceptional-component bound (4), especially a
   component with unused forward attachments or both initial and final tails.
5. Instantiate the theorem on the alternating-ladder equality cases and the
   off-corridor tight signatures listed in `lemma_rl_proof.md`.
6. Re-run the exhaustive SE1/SE2 fixtures.  Computational agreement is only
   falsification support; the proof above must stand independently.
