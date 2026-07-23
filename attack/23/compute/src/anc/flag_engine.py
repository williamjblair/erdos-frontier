#!/usr/bin/env python3
"""
Flag-algebra engine (Razborov) for graphs — built from scratch, heavily self-checked.
Stage 1: graph utilities (bitmask adjacency, canonical form, induced subgraphs, triangle-free).
Stage 2: enumeration of graphs up to iso + subgraph densities p(H_small; H_big).

Graph G = (n, A) with A a list of int bitmasks: bit j of A[i] set iff edge i~j (symmetric, no loops).
Canonical form = lexicographically-min upper-triangle bit tuple over all n! relabelings (brute, n<=7).
For flags, vertices 0..k-1 are LABELED roots; canonicalization may only permute the k..n-1 free vertices.
"""
import itertools
from functools import lru_cache

# ---------- basic graph ops ----------
def adj_from_edges(n, edges):
    A = [0]*n
    for (i, j) in edges:
        A[i] |= 1 << j; A[j] |= 1 << i
    return A

def edges_of(n, A):
    return [(i, j) for i in range(n) for j in range(i+1, n) if (A[i] >> j) & 1]

def num_edges(n, A):
    return sum(bin(A[i]).count('1') for i in range(n)) // 2

def has_edge(A, i, j):
    return (A[i] >> j) & 1

def is_triangle_free(n, A):
    for i in range(n):
        Ni = A[i]
        # any edge between two neighbors of i?
        for j in range(i+1, n):
            if (Ni >> j) & 1:
                if A[i] & A[j]:  # common neighbor => triangle
                    return False
    return True

def induced(A, verts):
    """Induced subgraph on the ordered list `verts`; returns (k, B) with new labels 0..k-1."""
    k = len(verts)
    idx = {v: a for a, v in enumerate(verts)}
    B = [0]*k
    for a in range(k):
        va = verts[a]
        for b in range(a+1, k):
            if (A[va] >> verts[b]) & 1:
                B[a] |= 1 << b; B[b] |= 1 << a
    return k, B

def _bits_upper(n, A):
    out = []
    for i in range(n):
        for j in range(i+1, n):
            out.append((A[i] >> j) & 1)
    return tuple(out)

def relabel(n, A, perm):
    """Return adjacency after mapping vertex i -> perm[i]."""
    B = [0]*n
    for i in range(n):
        pi = perm[i]
        Ai = A[i]
        j = 0; x = Ai
        while x:
            if x & 1:
                B[pi] |= 1 << perm[j]
            x >>= 1; j += 1
    return B

def canonical(n, A, roots=0):
    """Lex-min upper-triangle tuple over relabelings that FIX the first `roots` vertices.
    Returns a hashable canonical key (the bit tuple). roots=0 => full iso class."""
    best = None
    free = list(range(roots, n))
    for p in itertools.permutations(free):
        perm = list(range(roots)) + list(p)
        B = relabel(n, A, perm)
        t = _bits_upper(n, B)
        if best is None or t < best:
            best = t
    return best

def graph_from_key(n, key):
    """Inverse of _bits_upper: build adjacency from an upper-triangle bit tuple."""
    A = [0]*n; idx = 0
    for i in range(n):
        for j in range(i+1, n):
            if key[idx]:
                A[i] |= 1 << j; A[j] |= 1 << i
            idx += 1
    return A

# ---------- enumeration up to iso ----------
import os, subprocess
GENG = os.path.join(os.path.dirname(__file__), "..", "..", "tools", "nauty2_8_9", "geng.exe")

def _decode_g6(s):
    data = [ord(c) - 63 for c in s.strip()]; n = data[0]; bits = []
    for d in data[1:]:
        for k in range(5, -1, -1): bits.append((d >> k) & 1)
    A = [0]*n; idx = 0
    for j in range(1, n):
        for i in range(j):
            if idx < len(bits) and bits[idx]:
                A[i] |= 1 << j; A[j] |= 1 << i
            idx += 1
    return n, A

def enumerate_graphs(n, triangle_free=True):
    """All graphs on n vertices up to iso (optionally triangle-free) via geng. Returns [(n,A)]."""
    if n == 0:
        return [(0, [])]
    if n == 1:
        return [(1, [0])]
    args = [GENG]
    if triangle_free: args.append("-t")
    args += [str(n)]
    out = subprocess.run(args, capture_output=True, text=True).stdout
    res = []
    for line in out.splitlines():
        if line.strip():
            res.append(_decode_g6(line))
    return res

def enumerate_graphs_brute(n, triangle_free=True):
    """Brute enumeration up to iso (small n only, for cross-checking geng)."""
    seen = {}
    m = n*(n-1)//2
    for mask in range(1 << m):
        key0 = tuple((mask >> b) & 1 for b in range(m))
        A = graph_from_key(n, key0)
        if triangle_free and not is_triangle_free(n, A):
            continue
        ck = canonical(n, A)
        if ck not in seen:
            seen[ck] = graph_from_key(n, ck)
    return [(n, A) for A in seen.values()]

# ---------- densities ----------
def induced_density(small, big):
    """p(small; big) = P[random |small|-subset of big induces a graph iso to `small`].
    small=(k,As) canonicalized internally; big=(n,Ab)."""
    k, As = small; n, Ab = big
    if k > n: return 0.0
    target = canonical(k, As)
    cnt = 0; tot = 0
    for verts in itertools.combinations(range(n), k):
        kk, B = induced(Ab, list(verts))
        tot += 1
        if canonical(kk, B) == target:
            cnt += 1
    return cnt / tot if tot else 0.0

# ---------- self-tests ----------
if __name__ == "__main__":
    # counts of triangle-free graphs up to iso (OEIS A006785): n=1..7 -> 1,2,3,7,14,38,107
    expect = {1:1, 2:2, 3:3, 4:7, 5:14, 6:38, 7:107}
    print("triangle-free graph counts up to iso:")
    ok = True
    for n in range(1, 8):
        c = len(enumerate_graphs(n, triangle_free=True))
        good = (c == expect[n]); ok &= good
        print(f"  n={n}: {c}  (expect {expect[n]})  {'OK' if good else 'MISMATCH'}")
    # all graphs up to iso (A000088): 1,2,4,11,34,156
    expect_all = {1:1,2:2,3:4,4:11,5:34,6:156}
    print("all graph counts up to iso:")
    for n in range(1,7):
        c = len(enumerate_graphs(n, triangle_free=False)); good=(c==expect_all[n]); ok&=good
        print(f"  n={n}: {c} (expect {expect_all[n]}) {'OK' if good else 'MISMATCH'}")
    # cross-check geng vs brute (n<=5): same canonical set
    print("geng vs brute cross-check (n<=5, triangle-free):")
    for n in range(2,6):
        sg = {canonical(n,A) for (_,A) in enumerate_graphs(n,True)}
        sb = {canonical(n,A) for (_,A) in enumerate_graphs_brute(n,True)}
        good=(sg==sb); ok&=good
        print(f"  n={n}: geng={len(sg)} brute={len(sb)} {'OK' if good else 'MISMATCH'}")
    # density sanity: edge density of C5 = 5 edges / C(5,2)=10 -> p(K2;C5)=0.5
    edge = (2, adj_from_edges(2, [(0,1)]))
    C5 = (5, adj_from_edges(5, [(i,(i+1)%5) for i in range(5)]))
    de = induced_density(edge, C5)
    print(f"edge density of C5 = {de}  (expect 0.5)  {'OK' if abs(de-0.5)<1e-9 else 'BAD'}")
    # densities of all order-2 graphs in C5 sum to 1
    g2 = enumerate_graphs(2, False)
    s = sum(induced_density(g, C5) for g in g2)
    print(f"sum of order-2 densities in C5 = {s}  (expect 1.0)  {'OK' if abs(s-1)<1e-9 else 'BAD'}")
    print("ALL OK" if ok else "SOME MISMATCH")
