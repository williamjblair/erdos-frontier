"""Random walk in the valid-K_25 space via free single-edge recolorings,
tracking the counting certificate sum h_c — a stress test of the target
lemma (sum h_c > 25) on colorings far from SLS attractors.

Every visited coloring is verified valid; every h-eval coloring gets an
extension SAT too (a SAT there = counterexample path).

Usage: python3 walk25.py <start best.txt|ag> <steps> <h_every> <seed>
"""
import random
import sys
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from w3_extend import E25, EIDX25, ag_coloring, check_valid_k25, extension_sat
from w3_certificate import class_graph, min_admissible_hitting_set

SIX = list(combinations(range(25), 6))
SIX_EDGES = [[EIDX25[e] for e in combinations(S, 2)] for S in SIX]
EDGE_SIXES = [[] for _ in range(300)]
for si, ks in enumerate(SIX_EDGES):
    for k in ks:
        EDGE_SIXES[k].append(si)


def main(start, steps, h_every, seed):
    rng = random.Random(seed)
    if start == 'ag':
        col = ag_coloring()
    else:
        lines = open(start).read().split('\n')
        assert int(lines[0]) == 0
        col = list(map(int, lines[1].split()))
    assert check_valid_k25(col) == 0

    cnt = [[0] * 5 for _ in range(len(SIX))]
    for si, ks in enumerate(SIX_EDGES):
        row = cnt[si]
        for k in ks:
            row[col[k]] += 1

    best_sum = None
    for step in range(steps + 1):
        if step % h_every == 0:
            hs = []
            for c in range(5):
                h, _, _, _ = min_admissible_hitting_set(class_graph(col, c))
                hs.append(h)
            tot = sum(hs)
            att = extension_sat(col, verbose=False)
            sizes = sorted(sum(1 for k in range(300) if col[k] == c)
                           for c in range(5))
            if best_sum is None or tot < best_sum:
                best_sum = tot
            print(f'step {step}: sizes={sizes} h={hs} sum={tot} '
                  f'(min seen {best_sum}) ext='
                  f'{"SAT!!!" if att is not None else "UNSAT"}', flush=True)
            if att is not None:
                print('!!!! EXTENDABLE VALID K25 FOUND ON WALK !!!!',
                      flush=True)
                print('coloring:', ' '.join(map(str, col)), flush=True)
                return
            if step % (h_every * 10) == 0:
                assert check_valid_k25(col) == 0, 'walk left valid space!'
        # free edges under current counts
        free = [k for k in range(300)
                if all(cnt[si][col[k]] >= 2 for si in EDGE_SIXES[k])]
        if not free:
            print('RIGID: no free edges — walk stuck', flush=True)
            return
        k = rng.choice(free)
        old = col[k]
        new = rng.choice([c for c in range(5) if c != old])
        col[k] = new
        for si in EDGE_SIXES[k]:
            cnt[si][old] -= 1
            cnt[si][new] += 1


if __name__ == '__main__':
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
