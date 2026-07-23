"""Harvest driver: repeatedly generate valid K_25 colorings via sls25 from
random/circulant seeds, then extension-SAT + counting-certificate each one.

Every harvested K_25 that is 1-vertex-extendable would give a K_26
counterexample immediately (verified against core and saved).

Usage: python3 harvest.py <worker_id> <n_iterations>
Appends results to runs25/harvest.tsv (one row per valid K_25 found).
"""
import os
import subprocess
import sys
import time
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import core
from w3_extend import (E25, EIDX25, check_valid_k25, extension_sat, build_k26)
from w3_certificate import class_graph, min_admissible_hitting_set

BASE = '/Users/williamblair/personal/lean-proofs/compute617'
TSV = os.path.join(BASE, 'runs25', 'harvest.tsv')


def degseq(adj):
    return tuple(sorted(bin(m).count('1') for m in adj))


def main(worker, iters):
    wid = int(worker)
    for i in range(int(iters)):
        seed = 10000 * wid + i
        mode = '0' if i % 2 == 0 else '3'
        prefix = os.path.join(BASE, 'runs25', f'w{wid}_{i}')
        t0 = time.time()
        subprocess.run([os.path.join(BASE, 'sls25'), mode, str(seed), '0.12',
                        prefix, '900', '4', '40000', '600'],
                       capture_output=True, text=True)
        lines = open(prefix + '.best.txt').read().split('\n')
        best = int(lines[0])
        dt = time.time() - t0
        if best != 0:
            print(f'[w{wid}#{i}] no valid K25 in 900s (best={best})', flush=True)
            os.remove(prefix + '.best.txt')
            continue
        col25 = list(map(int, lines[1].split()))
        assert len(col25) == 300
        bad = check_valid_k25(col25)
        assert bad == 0, f'sls25 claimed 0 but python recount says {bad}'
        sizes = [sum(1 for k in range(300) if col25[k] == c)
                 for c in range(5)]
        # extension SAT
        attach = extension_sat(col25, verbose=False)
        ext = 'SAT' if attach is not None else 'UNSAT'
        if attach is not None:
            full = build_k26(col25, attach)
            rep = core.verify_and_report(full)
            print('EXTENSION SAT!!', rep, flush=True)
            if rep['is_counterexample']:
                import json
                with open(os.path.join(BASE, 'witness.json'), 'w') as f:
                    json.dump({'n': 26, 'r': 5, 'coloring': full,
                               'source': f'harvest w{wid}#{i}',
                               'report': rep}, f)
                print(f'!!!! WITNESS FOUND via harvest {prefix} !!!!', flush=True)
                return
        # counting certificate
        hs = []
        for c in range(5):
            adj = class_graph(col25, c)
            h, ni, ncl, _ = min_admissible_hitting_set(adj)
            hs.append(h)
        hsum = sum(hs)
        if attach is not None and hsum > 25:
            print('INCONSISTENCY: extension SAT but certificate says no!',
                  flush=True)
        pairs = sorted(zip(sizes, hs))
        row = (f'w{wid}\t{i}\tmode{mode}\t{dt:.0f}s\tsizes={sizes}\t'
               f'h={hs}\tpairs={pairs}\tsum_h={hsum}\text={ext}\t{prefix}')
        with open(TSV, 'a') as f:
            f.write(row + '\n')
        print(row, flush=True)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
