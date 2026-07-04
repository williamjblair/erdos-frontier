# A machine-facts formal-verification certificate

Notes toward certificate design for [Project Diderot](https://projectdiderot.com),
July 2026. Diderot's principle is that only humans may issue certificates; AI
agents cannot self-certify. This proposes a shape for the Formal Verification
certificate that keeps that principle exact while separating the two claims
that "formalised" currently runs together.

## Evidence and certificate are different things

The distinction that makes "only humans issue certificates" coherent:

- **Evidence** is reproducible and needs no human. A Lean proof compiles in a
  given toolchain, is `sorry`-free, uses a specific axiom set, and takes a
  specific set of Prop hypotheses as parameters. Anyone can re-derive these
  facts, an agent can generate them, and they carry no judgment.
- **A certificate** is a named human saying "I ran this and it reproduces, and
  I vouch for it." The accountability is the human's name.

An agent can produce the evidence; a human issues the certificate over it. That
is Diderot's rule, made mechanical.

## Why Formal Verification is doing two jobs

"A proof object exists and type-checks" is evidence. "The formalisation
captures the paper's claim, and the proof follows the paper's argument" is a
human judgment. These come apart:
[Erdős 650](https://erdos.constellate.science/finding.html?n=650) is a case
where the first held and the second did not, because the formalisation silently
repaired a gap the paper never fixed. A single "Formal Verification" badge
cannot carry both claims without one of them being read into the other.

So: two layers, and they map onto Nat Sothanaphan's credit / disclosure /
accountability axes.

| axis | where it lives | who is accountable |
|---|---|---|
| credit | authorship field (human, AI-assisted, agent co-author) | nobody vouches; it is a declaration |
| disclosure | the AI Tool Disclosure certificate | declared, not judged |
| accountability (mechanical) | **Formal Verification, evidence layer** — the facts below | reproducible; an agent may generate it |
| accountability (judgment) | **a faithfulness layer** — a human attests the formalisation matches the paper | a named human, with a method and transcript |

## The evidence layer: fields

A machine-facts formal-verification record carries:

| field | meaning |
|---|---|
| `subject.source_claim` | the informal claim being formalised (a URL, a paper + hash) |
| `subject.formal_statement` | the exact declaration name that is the formal statement |
| `subject.proof` | the proof object: pinned URL, host, and the toolchain it builds in |
| `checks.compiles` | the proof object type-checks in that toolchain |
| `checks.sorry_free` | no `sorry` in the proof |
| `checks.axioms_beyond_standard` | axioms the theorem depends on beyond the standard kernel set (`#print axioms`) |
| `checks.hypothesis_parameters` | the non-instance Prop hypotheses the theorem takes as parameters — the case an axiom check does not see |
| `verdict` | `unconditional` iff sorry-free **and** no non-standard axioms **and** no Prop hypothesis parameters; otherwise `conditional` |
| `reproduce` | the command to re-derive every field above from scratch |
| `generated_by` | the tool or agent that computed the facts (not a certifier) |

`hypothesis_parameters` is the field that does the work an axiom check misses: a
proof can be `sorry`-free and `#print axioms`-clean and still prove its goal
only under a deep theorem passed in as a hypothesis.

## Worked examples

Both generated mechanically by [`certificate.py`](certificate.py) from the
[audit feed](https://erdos.constellate.science/), no hand-editing.

**Unconditional** — [`certificates/erdos-16.evidence.json`](certificates/erdos-16.evidence.json):
`compiles: true`, `sorry_free: true`, no non-standard axioms, no hypothesis
parameters, so `verdict: unconditional`.

**Conditional** — [`certificates/erdos-997.evidence.json`](certificates/erdos-997.evidence.json):
compiles and is `sorry`-free, but depends on the axiom `maynardTaoBFT` (the
Maynard–Tao theorem, asserted rather than proved in the proof), so
`verdict: conditional`. A plain "formalised" badge would read as a full
solution; the evidence layer says exactly what it rests on.

```
python certificate.py 997
```

## The faithfulness layer

The human-judgment half is a separate attestation, not part of the mechanical
record. The [screening procedure](SCREENING.md) is one way to produce it: a
named reviewer works a per-clause table of formal statement against source, and
reports the result as "found no mismatch" or "claimed a mismatch in clause X",
never "faithful", with the transcript linked. It is not reproducible; it is a
signed judgment, and the reviewer's name is the accountability.

Stopgap while that layer is unbuilt: Formal Verification can honestly say "the
result is formalised, but the formalisation does not necessarily follow the
paper's argument."

## Reproduce

Every evidence record names its own reproduction. For the examples here:

```
# clone the pinned proof, build it in the stated toolchain, then in Lean:
#print axioms Erdos997.erdos_997
# and inspect the theorem's non-instance Prop parameters
```

or, through the audit's own extractor,
`python3 lean/extract_assumptions.py --repo plby`. The point of the evidence
layer is that a reader does not have to trust the certificate: they can re-run it.
