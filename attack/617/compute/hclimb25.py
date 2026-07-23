"""Descent on sum h_c over the valid-K_25 space (free-edge moves only).

Objective: sum over classes of h_c (min admissible hitting set; 999 = inf,
scored as 30 to keep gradients).  Batch of random free moves, evaluate,
accept if <= incumbent (plateau moves allowed), else revert.  Restart
perturbation after `stall` consecutive rejections.  Saves best coloring.

If sum <= 25 is ever reached: extension SAT attempted immediately; a SAT
there is verified against core on the built K_26 and saved as witness.

Usage: python3 hclimb25.py <start|ag> <evals> <batch> <seed> <out_prefix>
"""
import random
import sys
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
import core
from w3_extend import (E25, EIDX25, ag_coloring, check_valid_k25,
                       extension_sat, build_k26)
from w3_certificate import class_graph, min_admissible_hitting_set

SIX = list(combinations(range(25), 6))
SIX_EDGES = [[EIDX25[e] for e in combinations(S, 2)] for S in SIX]
EDGE_SIXES = [[] for _ in range(300)]
for si, ks in enumerate(SIX_EDGES):
    for k in ks:
        EDGE_SIXES[k].append(si)


def hsum(col):
    hs = []
    for c in range(5):
        h, _, _, _ = min_admissible_hitting_set(class_graph(col, c))
        hs.append(h)
    return hs, sum(30 if h == 999 else h for h in hs)


def main(start, evals, batch, seed, out_prefix):
    rng = random.Random(seed)
    col = ag_coloring() if start == 'ag' else \
        list(map(int, open(start).read().split('\n')[1].split()))
    assert check_valid_k25(col) == 0

    cnt = [[0] * 5 for _ in range(len(SIX))]
    for si, ks in enumerate(SIX_EDGES):
        row = cnt[si]
        for k in ks:
            row[col[k]] += 1

    def apply_move(k, new):
        old = col[k]
        col[k] = new
        for si in EDGE_SIXES[k]:
            cnt[si][old] -= 1
            cnt[si][new] += 1
        return old

    def random_free_batch(nmoves):
        undo = []
        for _ in range(nmoves):
            free = [k for k in range(300)
                    if all(cnt[si][col[k]] >= 2 for si in EDGE_SIXES[k])]
            k = rng.choice(free)
            new = rng.choice([c for c in range(5) if c != col[k]])
            undo.append((k, apply_move(k, new)))
        return undo

    def revert(undo):
        for k, old in reversed(undo):
            apply_move(k, old)

    hs, cur = hsum(col)
    best, best_col = cur, col[:]
    print(f'start: h={hs} score={cur}', flush=True)
    stall = 0
    for ev in range(evals):
        undo = random_free_batch(batch if stall < 40 else 3 * batch)
        hs, val = hsum(col)
        if val <= cur:
            if val < cur:
                stall = 0
            cur = val
            if val < best:
                best, best_col = val, col[:]
                assert check_valid_k25(col) == 0
                with open(out_prefix + '.best.txt', 'w') as f:
                    f.write('0\n' + ' '.join(map(str, col)) + '\n')
                print(f'eval {ev}: NEW BEST h={hs} sum={val}', flush=True)
                if val <= 25:
                    att = extension_sat(col, verbose=False)
                    print(f'  sum<=25! extension: '
                          f'{"SAT" if att else "UNSAT"}', flush=True)
                    if att is not None:
                        full = build_k26(col, att)
                        rep = core.verify_and_report(full)
                        print('  core:', rep, flush=True)
                        if rep['is_counterexample']:
                            import json
                            with open('witness.json', 'w') as f:
                                json.dump({'coloring': full,
                                           'source': f'hclimb {out_prefix}',
                                           'report': rep}, f)
                            print('!!!! WITNESS FOUND !!!!', flush=True)
                            return
        else:
            revert(undo)
            stall += 1
        if ev % 100 == 0:
            print(f'eval {ev}: cur={cur} best={best} stall={stall}',
                  flush=True)
    print(f'FINAL best sum h = {best}', flush=True)


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]),
         int(sys.argv[4]), sys.argv[5])
