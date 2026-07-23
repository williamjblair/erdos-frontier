"""common.py — shared exact utilities for gate-2 analysis of the Gamma-invariant
(Erdős #23, arXiv:2606.28041 §7).  All arithmetic exact (int / Fraction).

Conventions:
  * graph = (n, edges) with edges a list of (u,v), u<v, simple.
  * a *cut* is an int bitmask S over vertices 0..n-1; side(v) = (S>>v)&1.
    We normalise so vertex n-1 is on side 0 (bit clear) when enumerating.
  * M = monochromatic edges (same side), B = bichromatic edges (the cut graph).
"""
from fractions import Fraction
from collections import deque
from itertools import combinations


# ---------------------------------------------------------------- basic graph
def adj_masks(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return adj


def is_triangle_free(n, edges):
    adj = adj_masks(n, edges)
    for u, v in edges:
        if adj[u] & adj[v]:
            return False
    return True


def cut_value(n, adj, S):
    """Number of bichromatic edges for colouring S (exact, integer)."""
    full = (1 << n) - 1
    comp = full & ~S
    c = 0
    m = S
    while m:
        v = (m & -m).bit_length() - 1
        c += (adj[v] & comp).bit_count()
        m &= m - 1
    return c


def all_max_cuts(n, edges):
    """Exact brute force: (mc, [S...]) over all 2^(n-1) colourings
    (vertex n-1 fixed on side 0, so each cut appears once)."""
    adj = adj_masks(n, edges)
    best, args = -1, []
    for S in range(1 << (n - 1)):
        c = cut_value(n, adj, S)
        if c > best:
            best, args = c, [S]
        elif c == best:
            args.append(S)
    return best, args


def max_cut_value(n, edges):
    adj = adj_masks(n, edges)
    best = -1
    for S in range(1 << (n - 1)):
        c = cut_value(n, adj, S)
        if c > best:
            best = c
    return best


# ------------------------------------------------------------ instance = (G,S)
def split_edges(edges, S):
    M = [(u, v) for u, v in edges if ((S >> u) & 1) == ((S >> v) & 1)]
    B = [(u, v) for u, v in edges if ((S >> u) & 1) != ((S >> v) & 1)]
    return M, B


def bfs_dist(n, badj, src):
    dist = [-1] * n
    dist[src] = 0
    q = deque([src])
    while q:
        x = q.popleft()
        m = badj[x]
        while m:
            y = (m & -m).bit_length() - 1
            m &= m - 1
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                q.append(y)
    return dist


def b_connected(n, bedges):
    badj = adj_masks(n, bedges)
    if n == 0:
        return True
    reach = 1
    while True:
        new = reach
        m = reach
        while m:
            v = (m & -m).bit_length() - 1
            m &= m - 1
            new |= badj[v]
        if new == reach:
            break
        reach = new
    return reach == (1 << n) - 1


def gamma_of_instance(n, edges, S, require_connected=True):
    """Returns dict with M, B, per-edge B-distances, Gamma.  Asserts the derived
    side conditions (parity, >=4).  Raises if B disconnected and required."""
    M, B = split_edges(edges, S)
    badj = adj_masks(n, B)
    if require_connected:
        assert b_connected(n, B), "B not connected/spanning"
    dists = []
    g = 0
    for u, v in M:
        d = bfs_dist(n, badj, u)[v]
        assert d >= 0, "M-edge endpoints in different B-components"
        assert d % 2 == 0, "parity violation: d_B(u,v) odd for uv in M"
        assert d >= 4, "triangle-freeness violation: d_B(u,v) < 4"
        dists.append(d)
        g += (d + 1) ** 2
    return {"M": M, "B": B, "dists": dists, "Gamma": g, "N2": n * n}


def flip_condition_holds(n, edges, S):
    """Check max-cut characterisation directly: for all T (subsets with vertex
    n-1 excluded, WLOG by complementation), e_M(delta T) <= e_B(delta T)."""
    M, B = split_edges(edges, S)
    for T in range(1 << (n - 1)):
        em = sum(1 for u, v in M if ((T >> u) & 1) != ((T >> v) & 1))
        eb = sum(1 for u, v in B if ((T >> u) & 1) != ((T >> v) & 1))
        if em > eb:
            return False, T
    return True, None


# ------------------------------------------------------------- graph builders
def blowup(base_n, base_edges, sizes):
    """Blow-up with class sizes sizes[i]; returns (n, edges, classes)."""
    assert len(sizes) == base_n
    idx, classes = 0, []
    for s in sizes:
        classes.append(list(range(idx, idx + s)))
        idx += s
    edges = []
    for u, v in base_edges:
        for a in classes[u]:
            for b in classes[v]:
                edges.append((min(a, b), max(a, b)))
    return idx, edges, classes


def cycle(k):
    return k, [(i, (i + 1) % k) if i + 1 < k else (0, k - 1) for i in range(k)]


def c5_blowup(sizes):
    n5, e5 = cycle(5)
    return blowup(5, e5, sizes)


# --------------------------------------------------------------- graph6 codec
def parse_graph6(line):
    line = line.strip()
    assert line and ord(line[0]) - 63 < 63, "only short-form graph6 supported"
    n = ord(line[0]) - 63
    bits = []
    for ch in line[1:]:
        x = ord(ch) - 63
        for k in range(5, -1, -1):
            bits.append((x >> k) & 1)
    edges = []
    p = 0
    for j in range(1, n):
        for i in range(j):
            if bits[p]:
                edges.append((i, j))
            p += 1
    return n, edges


# ------------------------------------------------ shortest-path counting (B)
def sp_counts(n, badj, src):
    """BFS distances and shortest-path counts from src (exact ints)."""
    dist = [-1] * n
    cnt = [0] * n
    dist[src] = 0
    cnt[src] = 1
    q = deque([src])
    while q:
        x = q.popleft()
        m = badj[x]
        while m:
            y = (m & -m).bit_length() - 1
            m &= m - 1
            if dist[y] < 0:
                dist[y] = dist[x] + 1
                q.append(y)
                cnt[y] = cnt[x]
            elif dist[y] == dist[x] + 1:
                cnt[y] += cnt[x]
    return dist, cnt
