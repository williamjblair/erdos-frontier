"""Decode an smsg SAT witness (class-0 edge list) for a K_25 leg into a
full exactly-verified witness: fix class-0 edges as units in the ORIGINAL
leg encoding, re-solve (seconds), then run cube_common.verify_witness.

python3 decode_sms_witness.py <leg> "<edge-list-line>" <outdir>
edge-list-line: smsg output like [(0,7),(0,8),(1,4),...]
"""
import ast
import sys

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import cube_common as CC
import lemma_loud as LL
from pysat.solvers import Cadical195


def main():
    leg, line, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
    edges = set(tuple(sorted(e)) for e in
                ast.literal_eval(line.replace('(', '(').strip()))
    units = []
    for k, e in enumerate(LL.E25):
        v = CC.xvar(k, 0)
        units.append(v if e in edges else -v)
    cls, meta = CC.build_leg(leg)
    with Cadical195(bootstrap_with=cls) as s:
        r = s.solve(assumptions=units)
        print('re-solve with class-0 fixed:', r)
        assert r is True, 'smsg witness does not extend?! (bug somewhere)'
        rep = CC.verify_witness(leg, meta, s.get_model(), outdir)
    keep = {k: v for k, v in rep.items()
            if k not in ('coloring', 'k26_coloring', 'edges', 'H')}
    print('verification summary:', keep)


if __name__ == '__main__':
    main()
