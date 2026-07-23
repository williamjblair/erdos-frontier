"""Local-move structure of valid K_25 colorings.

An edge e is FREE iff recoloring it (to any other color) preserves validity:
recoloring e from c to c' only affects 6-sets containing e, where color c'
becomes present via e itself and color c survives iff some OTHER edge of the
6-set has color c.  So e is free  <=>  every 6-set containing e has >= 2
edges of color col(e).  Free edges = degree of the coloring in the
single-edge-move graph of the valid space (each free edge gives 4 moves).

Also reports, per coloring, the count of 6-sets with a unique edge of some
color ("critical" 6-sets) — 0 critical 6-sets through e <=> e free.

Usage: python3 freedom25.py <best.txt|ag|trans1> [...]
"""
import sys
from itertools import combinations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from w3_extend import E25, EIDX25, ag_coloring, check_valid_k25

SIX = list(combinations(range(25), 6))
SIX_EDGES = [[EIDX25[e] for e in combinations(S, 2)] for S in SIX]
EDGE_SIXES = [[] for _ in range(300)]
for si, ks in enumerate(SIX_EDGES):
    for k in ks:
        EDGE_SIXES[k].append(si)


def trans1_coloring():
    """rep#1 from trans_enum: orbit colors (0,0,3,2,1,1,4,3,1,2,4,4)."""
    a = (0, 0, 3, 2, 1, 1, 4, 3, 1, 2, 4, 4)
    orbit_of_diff = {}
    orb = []
    for da in range(5):
        for db in range(5):
            if (da, db) == (0, 0) or (da, db) in orbit_of_diff:
                continue
            o = len(orb)
            orbit_of_diff[(da, db)] = o
            orbit_of_diff[((-da) % 5, (-db) % 5)] = o
            orb.append((da, db))
    col = []
    for u, v in E25:
        d = ((u // 5 - v // 5) % 5, (u % 5 - v % 5) % 5)
        col.append(a[orbit_of_diff[d]])
    return col


def analyze(name, col):
    assert check_valid_k25(col) == 0, f'{name}: not a valid K25'
    cnt = [[0] * 5 for _ in range(len(SIX))]
    for si, ks in enumerate(SIX_EDGES):
        row = cnt[si]
        for k in ks:
            row[col[k]] += 1
    free = []
    for k in range(300):
        c = col[k]
        if all(cnt[si][c] >= 2 for si in EDGE_SIXES[k]):
            free.append(k)
    crit = sum(1 for si in range(len(SIX)) if any(x == 1 for x in cnt[si]))
    print(f'{name}: free_edges={len(free)} (moves={4*len(free)}) '
          f'critical_6sets={crit}'
          f'{" free=" + str([E25[k] for k in free[:12]]) if free else ""}',
          flush=True)
    return free


def load(path):
    lines = open(path).read().split('\n')
    assert int(lines[0]) == 0
    return list(map(int, lines[1].split()))


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        if arg == 'ag':
            analyze('AG', ag_coloring())
        elif arg == 'trans1':
            analyze('trans1', trans1_coloring())
        else:
            analyze(arg.rsplit('/', 1)[-1], load(arg))
