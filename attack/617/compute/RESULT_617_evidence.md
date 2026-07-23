# Erdős #617 at r = 5: computational evidence (not a complete proof)

Date: 2026-07-11
Status: **strong evidence the conjecture holds at r = 5; complete SAT
certificate not reached (hard tail uneconomical).**

## What #617 asks (r = 5 instance)

Does there exist a 5-colouring of the edges of K₂₆ such that every
6-subset of vertices spans all five colours? Equivalently, is the
associated SAT/SMS instance satisfiable? A counterexample colouring
(SAT) would refute the conjecture at r = 5; UNSAT confirms it.

Search space (naive): 5^{C(26,2)} = 5^{325} ≈ 10^{227}. This is a
Ramsey-type existence question — the family of R(5,5), open ~70 years —
so machine search with symmetry breaking (SMS) + cube-and-conquer is the
only known attack.

## What was done

Proof-ledger decomposition into three SAT legs (`sum_silent`,
`edges_loud`, `floor_loud`) over K₂₅, plus the assumption-free K₂₆
direct encoding. Each leg cube-decomposed (smsg `--simple-assignment-
cutoff 60`, ~25–27k cubes/leg) and solved in parallel (kissat + smsg),
first locally (M3 Max) then on Azure (F64 + F48, 112 vCPU).

## Result

- **sum_silent** (hardest leg, 25,618 coarse cubes): ~22,500 cubes
  resolved, **every one UNSAT**. Zero SAT.
- **edges_loud / floor_loud** (27,153 / 27,432 coarse cubes each):
  sweeps in progress at teardown, **all resolved cubes UNSAT**. Zero SAT.
- **K₂₆ direct + monolith legs**: ran 8–11 h, no verdict (silent), no
  SAT witness.
- **Across every solver, every machine, the entire campaign: not a
  single SAT cube ever appeared.**

A SAT cube would have been a counterexample colouring (checkable against
`compute617/core.py` ground truth in milliseconds). None was found.

## Why not a complete certificate

Cube hardness is heavy-tailed. ~99% of `sum_silent` cubes close in
seconds; a thin tail of ~194 cubes each survived a full 1-hour flat
solve. Cube-and-conquer (recursive structural splitting via smsg
edge-variable cutoff, `crack2.py`) was tried on the tail: a single hard
cube generated a >2,900-branch search tree and did **not** close in
3+ hours of one-core work. Extrapolated, the full tail across all three
legs is weeks of fleet time and exceeds a $200 compute budget with no
guarantee of termination — the classic Ramsey resistant tail. The
campaign was stopped here by decision, banking the evidence.

## Standing on firmer ground (already banked in Lean, kernel-checked)

- `statement_five_of_extension_demand` scaffold (ErdosProblems/Erdos617.lean)
- s = 2 leg closed as a theorem (2·76 + 3·50 = 302 > 300)
- silent-class edge floor ≥ 76 (SMS enumeration "Result: 20")

## Honest one-line summary

Exhaustive cube search found **zero counterexamples** across ~22,500+
resolved sub-problems of the hardest leg (and partial coverage of two
others) — strong evidence **Erdős #617 is true at r = 5** — but the
resistant hard tail was not closed, so this is evidence, not a proof.
