"""rl_lib.py — gate-3 shared utilities for Lemma RL (Erdős #23).

A one-stub rooted instance R = (B, M, w, x0) is:
  * B connected bipartite on n vertices,
  * M a set of internal edges: same side (even B-distance), d_B(u,v) >= 4,
    with B ∪ M simple and triangle-free,
  * a root w and a stub vertex x0 != w (sigma = 1 at x0),
subject to the rooted flip condition

    (RFC)  for all T ⊆ V \\ {w}:  e_M(δT) + [x0 ∈ T]  <=  e_B(δT).

Lemma RL:  Γ_int := Σ_{uv∈M} (d_B(u,v)+1)²  <=  s(2d+2+s) + 2s·p(d),
where d = d_B(x0,w), s = n−1−d, and p(d) the parity-minimal partner
distance: p(1)=3, p(2)=2, p(3)=1, p(even>=4)=2, p(odd>=5)=1.

All arithmetic exact (int / numpy int32 with tiny magnitudes).
"""
import sys, os, subprocess
from itertools import combinations
import numpy as np

BASE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(BASE, "..", "gate2"))
from common import parse_graph6, adj_masks, bfs_dist  # noqa: E402

GENG = "/opt/homebrew/bin/geng"


def p_of_d(d):
    """Parity-minimal admissible partner distance (sum even and >= 4)."""
    if d == 1:
        return 3
    if d == 2:
        return 2
    if d == 3:
        return 1
    return 2 if d % 2 == 0 else 1


def rl_rhs(n, d):
    s = n - 1 - d
    return s * (2 * d + 2 + s) + 2 * s * p_of_d(d)


# --------------------------------------------------------------- instance ops
def all_dists(n, edges):
    adj = adj_masks(n, edges)
    return [bfs_dist(n, adj, s0) for s0 in range(n)]


def m_candidates(n, dist):
    """All same-side pairs at B-distance >= 4 (distance even automatic)."""
    out = []
    for u in range(n):
        for v in range(u + 1, n):
            if dist[u][v] >= 4 and dist[u][v] % 2 == 0:
                out.append((u, v))
    return out


def union_triangle_free(n, edges, M):
    """B ∪ M triangle-free?  B-only triangles impossible (bipartite);
    B-B-M impossible (d_B >= 4); check M-M-B and M-M-M."""
    adjB = adj_masks(n, edges)
    adjM = [0] * n
    for u, v in M:
        adjM[u] |= 1 << v
        adjM[v] |= 1 << u
    for u, v in M:
        # third vertex adjacent (in B or M) to both u and v
        if (adjB[u] | adjM[u]) & (adjB[v] | adjM[v]):
            return False
    return True


def xor_bits(n):
    """bit[x] = numpy uint8 array over T in [0,2^n): (T>>x)&1."""
    T = np.arange(1 << n, dtype=np.uint32)
    return [((T >> x) & 1).astype(np.int32) for x in range(n)]


def slack_array(n, edges, M, bit):
    """slack(T) = e_B(δT) − e_M(δT) for all T (numpy int32, exact)."""
    sl = np.zeros(1 << n, dtype=np.int32)
    for a, b in edges:
        sl += bit[a] ^ bit[b]
    for a, b in M:
        sl -= bit[a] ^ bit[b]
    return sl


def valid_stub_pairs(n, slack):
    """Given slack(T) >= 0 for all T (unrooted S2 already holds), return the
    set of valid (w, x0) pairs for a single stub:
      (w,x0) valid  ⟺  every T with slack(T)=0, w∉T also has x0∉T.
    Returns an n×n boolean matrix ok[w][x0]."""
    Z = np.flatnonzero(slack == 0).astype(np.uint64)
    ok = np.ones((n, n), dtype=bool)
    np.fill_diagonal(ok, False)
    for w in range(n):
        Zw = Z[(Z >> np.uint64(w)) & np.uint64(1) == 0]
        if len(Zw):
            U = np.bitwise_or.reduce(Zw)
            for x in range(n):
                if (int(U) >> x) & 1:
                    ok[w][x] = False
    return ok


def gamma_of(M, dist):
    return sum((dist[a][b] + 1) ** 2 for a, b in M)


def check_rfc_direct(n, edges, M, w, x0):
    """Independent O(2^n) exact check of RFC (no numpy) — for spot audits."""
    for T in range(1 << n):
        if (T >> w) & 1:
            continue
        eB = sum(1 for a, b in edges if ((T >> a) & 1) != ((T >> b) & 1))
        eM = sum(1 for a, b in M if ((T >> a) & 1) != ((T >> b) & 1))
        sg = (T >> x0) & 1
        if eM + sg > eB:
            return False, T
    return True, None


# ----------------------------------------------------------------- generators
def gen_bipartite(n):
    out = subprocess.run([GENG, "-q", "-c", "-b", str(n)],
                         capture_output=True, text=True)
    return out.stdout.splitlines()


def geodesics_between(n, adj, dist, u, v):
    """All u–v geodesics (as vertex tuples).  Exponential in theory; fine for
    n <= 11 audit use."""
    D = dist[u][v]
    paths = [[u]]
    for step in range(D):
        nxt = []
        for pth in paths:
            x = pth[-1]
            m = adj[x]
            while m:
                y = (m & -m).bit_length() - 1
                m &= m - 1
                if dist[u][y] == step + 1 and dist[y][v] == D - step - 1:
                    nxt.append(pth + [y])
        paths = nxt
    return [tuple(p) for p in paths]
