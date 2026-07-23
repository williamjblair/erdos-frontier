"""Standalone-kissat stage for the hardest surviving cubes.

Writes base-CNF + cube units to a temp file per cube, runs
tools/kissat/build/kissat, verifies any SAT model exactly, logs verdicts.

python3 kissat_cubes.py --leg sum_silent --base runs/leg_sum_silent.cnf \
    --survivors runs/cubes_sum_silent/survivors.json --jobs 2 \
    --outdir runs/cubes_sum_silent [--time 3600]
"""
import argparse
import json
import os
import subprocess
import sys
import time
import multiprocessing as mp

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')

KISSAT = '/Users/williamblair/personal/lean-proofs/compute617/' \
    'tools/kissat/build/kissat'
TMPDIR = '/private/tmp/claude-501/-Users-williamblair-personal-lean-proofs/' \
    'dba4e108-9048-438a-a198-62aaba2b2adc/scratchpad'


def run_cube(task):
    leg, base_path, cube, timecap, outdir = task
    os.nice(10)
    with open(base_path, 'rb') as f:
        header = f.readline().decode()
        body = f.read()
    _, _, nv, ncl = header.split()
    lits = cube['lits']
    path = f'{TMPDIR}/{leg}_{cube["id"]}.cnf'
    with open(path, 'wb') as f:
        f.write(f'p cnf {nv} {int(ncl) + len(lits)}\n'.encode())
        f.write(body)
        f.write(''.join(f'{l} 0\n' for l in lits).encode())
    cmd = [KISSAT, path]
    if timecap:
        cmd.insert(1, f'--time={timecap}')
    t0 = time.time()
    r = subprocess.run(cmd, capture_output=True, text=True)
    wall = time.time() - t0
    os.unlink(path)
    if r.returncode == 10:
        model = []
        for line in r.stdout.splitlines():
            if line.startswith('v '):
                model += [int(x) for x in line[2:].split() if x != '0']
        import cube_common as CC
        _, meta = (None, {'kind': 'graph', 'hmap': None, 'leg': leg}) \
            if leg == 'silent_floor75' else CC.build_leg(leg)
        rep = CC.verify_witness(leg, meta, model, outdir)
        summary = {k: v for k, v in rep.items()
                   if k not in ('coloring', 'k26_coloring', 'edges', 'H')}
        return cube['id'], 'SAT', wall, summary
    if r.returncode == 20:
        return cube['id'], 'UNSAT', wall, None
    return cube['id'], 'UNKNOWN', wall, None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--leg', required=True)
    ap.add_argument('--base', required=True)
    ap.add_argument('--survivors', required=True)
    ap.add_argument('--jobs', type=int, default=2)
    ap.add_argument('--time', type=int, default=0)
    ap.add_argument('--outdir', required=True)
    args = ap.parse_args()
    cubes = json.load(open(args.survivors))
    tasks = [(args.leg, args.base, c, args.time, args.outdir) for c in cubes]
    res_path = f'{args.outdir}/kissat_results.tsv'
    with mp.Pool(args.jobs) as pool, open(res_path, 'a') as f:
        for cid, status, wall, summary in pool.imap_unordered(run_cube,
                                                              tasks):
            f.write(f'{cid}\tkissat\t{args.time}\t{status}\t{wall:.1f}\t'
                    f'{json.dumps(summary) if summary else ""}\n')
            f.flush()
            print(f'{cid}: {status} in {wall:.0f}s', flush=True)
            if status == 'SAT':
                print(f'*** SAT — see witness json in {args.outdir}; '
                      f'summary: {summary}', flush=True)


if __name__ == '__main__':
    mp.set_start_method('spawn')
    main()
