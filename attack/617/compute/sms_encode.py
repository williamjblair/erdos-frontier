"""SMS encodings: direct Erdos-617-style instances with native vertex
symmetry breaking on the class-0 graph.

smsg (tools/sat-modulo-symmetries/build/src/smsg) searches for a graph on n
vertices given side constraints in DIMACS, restricting to lex-minimal
adjacency matrices under S_n.  Soundness with our aux structure: the side
constraints (edge-color one-hot + per-(r+1)-set coverage) are invariant as
a set under any vertex permutation applied simultaneously to the SMS edge
vars (class 0) and the aux color vars, so every solution permutes to a
solution and restricting to lex-min class-0 representatives is exhaustive.

Variable layout (SMS requires edge vars = 1..C(n,2), row-major u<v lex):
  1..C(n,2)                : class-0 edge vars e_{u,v}
  then x_{e,c}, c=1..r-1   : aux color vars
Constraints: exactly-one(e0(e), x_{e,1..r-1}) per edge; for every
(r+1)-subset S and color c: some edge of S has color c.

Modes:
  r3  : n=10, r=3 calibration (known UNSAT ~222s pysat CDCL, ~110s kissat)
  r5  : n=26, r=5 — THE instance (prepared; run deliberately)

python3 sms_encode.py r3 runs/sms_r3_k10.cnf
python3 sms_encode.py r5 runs/sms_r5_k26.cnf
Run: tools/sat-modulo-symmetries/build/src/smsg -v <n> --dimacs <file>
"""
import sys
from itertools import combinations


def encode(n, r):
    edges = list(combinations(range(n), 2))
    eidx = {e: k for k, e in enumerate(edges)}
    ne = len(edges)
    # class 0: vars 1..ne (SMS edge var order: lex over u<v — verified
    # against pysms GraphEncodingBuilder: combinations(V, 2) order)
    e0 = lambda k: k + 1
    x = lambda k, c: ne + (r - 1) * k + c            # c in 1..r-1
    cls = []
    for k in range(ne):
        lits = [e0(k)] + [x(k, c) for c in range(1, r)]
        cls.append(lits)
        for a, b in combinations(lits, 2):
            cls.append([-a, -b])
    for S in combinations(range(n), r + 1):
        ks = [eidx[e] for e in combinations(S, 2)]
        cls.append([e0(k) for k in ks])
        for c in range(1, r):
            cls.append([x(k, c) for k in ks])
    return cls, ne + (r - 1) * ne


def add_color_lex(cls, nv, n, r):
    """First-occurrence lex chain over aux colors 1..r-1: color c may first
    appear only after color c-1 has appeared (along lex edge order).
    Sound on top of SMS vertex minimality: permuting colors 1..r-1 fixes
    the class-0 graph, so both reductions compose."""
    ne = n * (n - 1) // 2
    x = lambda k, c: ne + (r - 1) * k + c
    f = {}
    for c in range(1, r):
        for k in range(ne):
            nv += 1
            f[c, k] = nv
    for c in range(1, r):
        for k in range(ne):
            # definition: f_{c,k} <-> f_{c,k-1} | x_{k,c}
            if k == 0:
                cls.append([-f[c, 0], x(0, c)])
                cls.append([-x(0, c), f[c, 0]])
            else:
                cls.append([-f[c, k], f[c, k - 1], x(k, c)])
                cls.append([-f[c, k - 1], f[c, k]])
                cls.append([-x(k, c), f[c, k]])
    for c in range(2, r):
        cls.append([-x(0, c)])                    # c>1 cannot open
        for k in range(1, ne):
            cls.append([-x(k, c), f[c - 1, k - 1]])
    return cls, nv


def main():
    mode, out = sys.argv[1], sys.argv[2]
    n, r = {'r3': (10, 3), 'r5': (26, 5), 'r5cb': (26, 5)}[mode]
    cls, nv = encode(n, r)
    if mode.endswith('cb'):
        cls, nv = add_color_lex(cls, nv, n, r)
    with open(out, 'w') as f:
        f.write(f'p cnf {nv} {len(cls)}\n')
        for c in cls:
            f.write(' '.join(map(str, c)) + ' 0\n')
    print(f'{mode}: n={n} r={r} vars={nv} clauses={len(cls)} -> {out}')
    print(f'run: tools/sat-modulo-symmetries/build/src/smsg -v {n} '
          f'--dimacs {out}')


if __name__ == '__main__':
    main()
