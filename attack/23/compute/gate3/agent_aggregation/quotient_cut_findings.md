# Component-quotient averaging for BF-RL

Status: **PROVED simultaneous cut reduction; not a proof of BF-RL.**  The
result controls every M-edge visible in the quotient by the components of
`B-V(P)`, and explicitly identifies the omitted recursive mass (M-edges
internal to one off-corridor component).  It never asserts a multicommodity
routing or a per-vertex load bound.

## 1. Exact setup and partition

Let `(B,M,w,x0)` be any valid one-stub rooted instance and fix a geodesic

```text
P = (u_0=w,u_1,...,u_d=x0).
```

Put `F=V(B)-V(P)`, `s=|F|`, and let `C_1,...,C_c` be the connected
components of the induced graph `B[F]`.  The cells of the quotient are the
off-corridor components `C_j` and the individual path vertices `u_i`.
Write

```text
A = e_B(F,V(P)).
```

Partition `M` into three disjoint classes:

1. `M_comp`: both endpoints lie in the same `C_j` (omitted by the quotient);
2. `M_P`: both endpoints lie on `P`;
3. `M_mix`: one endpoint lies on `P` and the other in a `C_j`, or the two
   endpoints lie in distinct off-corridor components.

Thus `M_mix` does **not** include an edge internal to one `C_j`, and it does
**not** include an edge with both endpoints on `P`.

Because `P` is geodesic, it is induced in `B`: a B-edge between two
nonconsecutive path vertices would shorten the corresponding subpath.  Also
there is no B-edge between distinct `C_j` by their definition.

## 2. Per-suffix quotient inequality

For `1<=r<=d`, let `P_r={u_r,...,u_d}` and let `k_r` be the number of
M-edges in `M_P` with path coordinates straddling `r`.  For every subset
`J subseteq {1,...,c}`, apply RFC to

```text
T_{r,J} = P_r union union_{j in J} C_j.
```

The root is outside and the stub is inside every such cut.  Sum the `2^c`
inequalities over `J`.

On the B side:

- the unique path edge `u_{r-1}u_r` crosses in all `2^c` choices;
- a B attachment edge between `C_j` and `P` crosses in exactly `2^(c-1)`
  choices;
- B-edges internal to `P_r`, its prefix, or one whole `C_j` never cross.

Hence the summed B side is

```text
2^c + 2^(c-1) A.
```

On the M side:

- every edge in `M_mix` crosses in exactly `2^(c-1)` choices;
- every one of the `k_r` path M-edges crosses in all `2^c` choices;
- every edge in `M_comp` crosses in none;
- the stub contributes one in all `2^c` choices.

The summed RFC inequality is therefore

```text
2^(c-1)|M_mix| + 2^c k_r + 2^c
  <= 2^c + 2^(c-1)A.
```

Cancelling and dividing by `2^(c-1)` proves the exact simultaneous bound

```text
|M_mix| + 2 k_r <= A.                                  (Q_r)
```

Here `c>=1` whenever `s>0`; BF-RL has `s>=5`.  The `s=0` case is already
banked separately and needs no division convention.

## 3. Attachment and summed bounds

Every `f in F` has at most two P-neighbours.  Indeed, if `f` is adjacent to
`u_i,u_j`, geodesicity gives `|i-j|=d_B(u_i,u_j)<=2`; bipartiteness makes
`|i-j|` even, so two distinct neighbours must occur at coordinates differing
by exactly two.  Counting attachment edges at their F endpoint gives

```text
A <= 2s.                                                (A)
```

Sum `(Q_r)` over `r=1,...,d`.  A path M-edge `u_i u_j` crosses exactly
`|i-j|=d_B(u_i,u_j)` suffix cuts, so

```text
d|M_mix| + 2 sum_{uv in M_P} d_B(u,v) <= dA <= 2ds.     (Q_sum)
```

This is a multiplicity-sensitive statement: a path edge of distance `D`
is counted exactly `D` times.  It does not sum the single-edge SE bounds.

## 4. Stronger arbitrary-path-subset form

The same average works for every `U subseteq V(P)`, not just a suffix.  Let
`b_P(U)` be the number of path edges crossing `U`, let `m_P(U)` be the
number of edges of `M_P` crossing `U`, and let `q(U)` indicate that `U`
separates `u_0,u_d`.  Averaging symmetric RFC over

```text
U union union_{j in J} C_j
```

gives

```text
|M_mix| + 2m_P(U) + 2q(U) <= A + 2b_P(U).              (Q_U)
```

If the displayed cut contains the root, symmetric RFC is old RFC on its
complement, so no extra hypothesis is used.  Equation `(Q_U)` is an exact
defect cut condition on the path quotient; `(Q_r)` is its suffix
specialization, where `b_P=q=1`.

## 5. A closed strict graph subregime

Suppose every M-edge is in `M_comp` and no `C_j` contains two M-edges.  If
edge `i` lies in a component of order `q_i`, connectedness of `C_j` supplies
an internal path of length at most `q_i-1`, hence

```text
D_i+1 <= q_i.
```

The owning components are distinct and the components partition F, so
`sum_i q_i<=s`.  Therefore

```text
sum_i (D_i+1)^2 <= sum_i q_i^2
                      <= (sum_i q_i)^2
                      <= s^2
                      <= RL-budget(s,d).
```

The arithmetic implication is kernel checked as
`totalCost_le_rlBudget_of_disjoint_componentResources` in
`Erdos23QuotientAggregation.lean`; its axiom report is exactly
`[propext, Classical.choice, Quot.sound]`.  This is a genuine bridge-free
subregime beyond the old series slice, but it does not handle a component
containing multiple M-edges or any quotient-visible M-edge.

## 6. Exact reproduction and hostile fixtures

`test_quotient_cut_average.py` checks:

- every averaged RFC cut and both closed-form sums on a long-tail
  `C5[3]` fixture and a long-thin `C9` fixture;
- every averaged cut on the banked mixed-distance series fixture;
- all `5,938` valid rooted `|M|=2` instances through `n=9` (one
  deterministic geodesic for every root/stub pair), totaling `8,322`
  suffix inequalities;
- the n=8 forced-hub and n=12 path-packing witnesses have **no** valid
  nontrivial stub pair (checked exactly from every zero-slack cut), so they
  are outside the rooted hypothesis rather than silently ignored.

All computations are integer/Boolean arithmetic.  The mathematical proof
above is independent of the finite check and applies to every geodesic.

## 7. Exact recursive frontier exposed

The quotient average loses exactly the M-edges internal to one `C_j`.
For such an edge the ambient distance is at most its within-component
distance and hence at most `|C_j|-1`, but RFC restricted to `C_j` contains
boundary attachment capacity.  Consequently `(B[C_j],M[C_j])` need not be
a valid smaller unrooted instance; invoking Gamma on it without proving
that validity would be circular.  Contracting the corridor preserves the
cut condition but can shorten M-distances below four and create triangles,
so same-order or contracted Gamma cannot be inserted here either.

Thus the next non-circular step is a boundary-aware recursive estimate for
components containing at least two internal M-edges, together with a
quadratic strengthening of `(Q_U)` for quotient-visible edges.  Neither is
asserted in this note.
