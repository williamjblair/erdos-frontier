"""Classify harvested valid K_25 colorings up to isomorphism
(vertex permutation x color permutation).

Two-stage: (1) invariant fingerprint (cheap, iso-invariant); (2) within
fingerprint groups, exact colored-iso via color-degree-profile-seeded
backtracking (complete graphs with edge colors: vertex map must preserve
all 300 edge colors under some color permutation).

Fingerprint per coloring: sorted tuple over the 5 classes of
 (edges, sorted degseq, triangles, ind5count, cl5count)
plus the sorted 25-vector of sorted per-vertex color-degree multisets.
"""
import glob
import sys
from itertools import combinations, permutations

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')
from w3_extend import E25, EIDX25, ag_coloring
from w3_certificate import class_graph, enum_independent_5sets, enum_5cliques

POPC = bin


def triangles(adj):
    t = 0
    for u, v in E25:
        if adj[u] >> v & 1:
            t += bin(adj[u] & adj[v]).count('1')
    return t // 3


def fingerprint(col):
    per = []
    for c in range(5):
        adj = class_graph(col, c)
        deg = tuple(sorted(bin(m).count('1') for m in adj))
        per.append((sum(deg) // 2, deg, triangles(adj),
                    len(enum_independent_5sets(adj)), len(enum_5cliques(adj))))
    per_sorted = tuple(sorted(per))
    # vertex profiles: multiset over vertices of sorted color-degree tuple
    adjs = [class_graph(col, c) for c in range(5)]
    prof = tuple(sorted(tuple(sorted(bin(adjs[c][v]).count('1')
                                     for c in range(5)))
                        for v in range(25)))
    return per_sorted, prof


def canonical_edge_colors(col):
    """map: (u,v) -> color"""
    return {e: col[k] for e, k in EIDX25.items()}


def iso_colored(colA, colB):
    """exact test: exists vertex perm p and color perm s with
    s(colA[{u,v}]) == colB[{p(u),p(v)}] for all edges."""
    adjA = [class_graph(colA, c) for c in range(5)]
    adjB = [class_graph(colB, c) for c in range(5)]
    degA = [[bin(adjA[c][v]).count('1') for c in range(5)] for v in range(25)]
    degB = [[bin(adjB[c][v]).count('1') for c in range(5)] for v in range(25)]
    eA = canonical_edge_colors(colA)
    eB = canonical_edge_colors(colB)

    def ecolA(u, v):
        return eA[(u, v) if u < v else (v, u)]

    def ecolB(u, v):
        return eB[(u, v) if u < v else (v, u)]

    for s in permutations(range(5)):
        # color perm s applied to A; match vertex profiles
        profA = [tuple(dv[c] for c in range(5)) for dv in degA]
        profAs = [tuple(profA[v][si] for si in inverse(s)) for v in range(25)]
        profB = [tuple(dv) for dv in degB]
        if sorted(profAs) != sorted(profB):
            continue
        # backtracking vertex map, most-constrained-first by profile rarity
        order = sorted(range(25), key=lambda v: profAs.count(profAs[v]))
        used = [False] * 25
        mapping = [-1] * 25

        def bt(i):
            if i == 25:
                return True
            u = order[i]
            for w in range(25):
                if used[w] or profB[w] != profAs[u]:
                    continue
                ok = True
                for j in range(i):
                    u2 = order[j]
                    if s[ecolA(u, u2)] != ecolB(w, mapping[u2]):
                        ok = False
                        break
                if ok:
                    mapping[u] = w
                    used[w] = True
                    if bt(i + 1):
                        return True
                    used[w] = False
            return False

        if bt(0):
            return True
    return False


def inverse(s):
    inv = [0] * len(s)
    for i, x in enumerate(s):
        inv[x] = i
    return inv


def load(path):
    lines = open(path).read().split('\n')
    if int(lines[0]) != 0:
        return None
    col = list(map(int, lines[1].split()))
    assert len(col) == 300
    return col


def main():
    files = sorted(glob.glob(
        '/Users/williamblair/personal/lean-proofs/compute617/runs25/*.best.txt'))
    items = [('AG', ag_coloring())]
    for f in files:
        col = load(f)
        if col is not None:
            items.append((f.rsplit('/', 1)[1].replace('.best.txt', ''), col))
    print(f'{len(items)} valid K_25 colorings loaded (incl. AG)', flush=True)

    groups = {}
    for name, col in items:
        fp = fingerprint(col)
        groups.setdefault(fp, []).append((name, col))
    print(f'{len(groups)} distinct fingerprints', flush=True)

    nclasses = 0
    for fp, members in sorted(groups.items(),
                              key=lambda kv: -len(kv[1])):
        # split members into exact iso classes
        reps = []
        for name, col in members:
            placed = False
            for rep in reps:
                if iso_colored(rep[1], col):
                    rep[2].append(name)
                    placed = True
                    break
            if not placed:
                reps.append((name, col, [name]))
        for rep in reps:
            nclasses += 1
            sizes = sorted(sum(1 for k in range(300) if rep[1][k] == c)
                           for c in range(5))
            print(f'iso-class #{nclasses}: sizes={sizes} '
                  f'members({len(rep[2])})={rep[2][:6]}'
                  f'{"..." if len(rep[2]) > 6 else ""}', flush=True)
    print(f'TOTAL: {len(items)} colorings -> {nclasses} iso classes',
          flush=True)


if __name__ == '__main__':
    main()
