# Erdős #23 gap G-A: kernel closure

Status: **Lean-complete; independent hostile audit passed.**

The audited paper component ledger is now realized by the kernel without a
remaining graph-construction hypothesis.

## Dependency tree

```text
G-A  SE1 and SE2 under the symmetric two-demand cut condition       PROVED
 |
 +-- every common nonbridge corridor edge has a covering component  PROVED
 +-- common visits are globally monotone up to orientation          PROVED
 +-- unit transitions biject with actually ridden coordinates       PROVED
 +-- nonunit transitions select their actual excursion component    PROVED
 +-- distinct transition gap intervals are disjoint                 PROVED
 +-- assigned ride plus excursion gap packs in component span       PROVED
 +-- qexc=0 implies no assigned excursion                            PROVED
 +-- exceptional qexc=r=0 tail has assigned rides <=q_C             PROVED
 +-- canonical component records sum to the exact global ledger     PROVED
 `-- forward and swapped ledgers imply SE1 and SE2                   PROVED
```

The substantial construction is in
`ErdosProblems/Erdos23GapGACanonical.lean`.  The final composition in
`ErdosProblems/Erdos23GapGAClosed.lean` proves

```text
gapGA_symmetric_bounds:
  Q.length <= 2*slack P /\
  2*Q.length <= 2*slack P + P.length.
```

## Repaired exceptional tail

The proof retains the exact witness that refuted the earlier claim
`C={4}, A_C={0,2}, q_C=1`.  It uses only the repaired inequality.

If an exceptional component had more assigned ridden edges than `q_C`,
interval packing and the geodesic component-span bound would both be tight:

```text
rides = span = q_C+1.
```

Thus every edge in the extreme attachment interval would be ridden.  Both
extreme attachment vertices would lie on `Q`.  Since `r_C=0`, every component
vertex also lies on `Q`; since `qexc_C=0`, all of them lie in the initial or
final tails.  Same-tail placements collapse the two distinct extreme
corridor coordinates.  Opposite-tail placements make the `Q`-index distance
between two component vertices exceed the maximum distance allowed inside a
connected `q_C`-vertex component.  Both alternatives contradict geodesicity.

This proves the exact exceptional dispatch `rides<=q_C`; it does not restore
the false assertion that an exceptional component has no forward attachment.

## Scope

This closes the prompt's allowed Gap G-A alternative and therefore the
rooted `|M|=1` case.  It does not prove the remaining multi-edge RL* regime or
the conjecture-strength 2-connected core.

The independent replay checked 89,016 SE1 and 89,016 SE2 instances, 136,712
G1/MSL instances, and 57 frontier triples through order eleven, with zero
failures.  Both Lean modules compile with `--trust=0`; every principal surface
uses only `[propext, Classical.choice, Quot.sound]`.

## Reproduction

```bash
lake env lean --trust=0 ErdosProblems/Erdos23GapGACanonical.lean
lake env lean --trust=0 ErdosProblems/Erdos23GapGAClosed.lean
lake build ErdosProblems.Erdos23GapGACanonical
lake build ErdosProblems.Erdos23GapGAClosed
python3 -m pytest compute23/gate3/test_gap_ga_component_ledger.py -q
```
