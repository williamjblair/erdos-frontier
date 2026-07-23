"""Materialize per-kind cube files from graph representatives.

python3 gen_cubes.py cubes/w7_reps.json 7 colored cubes/w7_colored.json
python3 gen_cubes.py cubes/w7_reps.json 7 graph   cubes/w7_graph.json
"""
import json
import sys

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import cube_common as CC


def main():
    reps_path, m, kind, out = sys.argv[1], int(sys.argv[2]), sys.argv[3], \
        sys.argv[4]
    reps = json.load(open(reps_path))
    cubes = []
    for i, r in enumerate(reps):
        lits = CC.cube_literals(kind, m, [tuple(e) for e in r['edges']])
        cubes.append({'id': f'r{i}', 'lits': lits,
                      'nedges': len(r['edges']), 'aut': r['aut_size']})
    # order: put structured (dense) patterns first — if anything is SAT it
    # is likelier dense (silent classes have >= 67 of 300 edges globally)
    cubes.sort(key=lambda c: -c['nedges'])
    with open(out, 'w') as f:
        json.dump(cubes, f)
    print(f'{len(cubes)} cubes ({kind}, window {m}) -> {out}')


if __name__ == '__main__':
    main()
