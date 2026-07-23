"""Deepen surviving cubes: window {0..6} -> {0..7}.

A depth-8 cube fixes the full class-0 pattern on {0..7} = parent pattern P
on {0..6} plus the neighborhood N of vertex 7 inside {0..6}.  For a parent
with pattern P it suffices to take one N per orbit of Aut(P) acting on
subsets of {0..6}: any solution with pattern P maps to one with N = orbit
representative by an automorphism of P extended identically — all leg
constraints are S_25-invariant (cube_common.py docstring).

python3 make_children.py cubes/w7_reps.json runs/cubes_<leg>/survivors.json \
    colored cubes/<leg>_w8_children.json
"""
import json
import sys

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import cube_common as CC
from graph_reps import aut_size_and_orbits


def main():
    reps_path, survivors_path, kind, out = sys.argv[1:5]
    reps = json.load(open(reps_path))
    survivors = json.load(open(survivors_path))
    children = []
    for s in survivors:
        i = int(s['id'].lstrip('r').split('_')[0])
        r = reps[i]
        edges = [tuple(e) for e in r['edges']]
        mask = 0
        el = [tuple(sorted(e)) for e in edges]
        from itertools import combinations
        eidx = {e: j for j, e in enumerate(combinations(range(7), 2))}
        for e in el:
            mask |= 1 << eidx[e]
        aut, orbit_reps = aut_size_and_orbits(7, mask)
        for nb in orbit_reps:
            ext = edges + [(u, 7) for u in range(7) if (nb >> u) & 1]
            lits = CC.cube_literals(kind, 8, ext)
            children.append({'id': f'{s["id"]}_n{nb}', 'lits': lits,
                             'nedges': len(ext), 'aut': aut})
    children.sort(key=lambda c: -c['nedges'])
    with open(out, 'w') as f:
        json.dump(children, f)
    print(f'{len(survivors)} survivors -> {len(children)} depth-8 children '
          f'-> {out}')


if __name__ == '__main__':
    main()
