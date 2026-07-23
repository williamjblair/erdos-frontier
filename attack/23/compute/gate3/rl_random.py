"""rl_random.py — fresh random rooted one-stub instances, exact arithmetic.

Random connected bipartite B on n in [NLO, NHI]; random M subsets of the
candidate pairs (rejection-sampled against the unrooted flip condition and
triangle-freeness of B ∪ M); all valid (w, x0) rootings found exactly; then
RL, SE1, SE2 checked for every rooting and every M-edge.

Usage: python3 rl_random.py NLO NHI TRIALS SEED
"""
import sys, random, time
from itertools import combinations
import numpy as np
from rl_lib import (adj_masks, bfs_dist, p_of_d, rl_rhs, all_dists,
                    m_candidates, union_triangle_free, xor_bits,
                    valid_stub_pairs, gamma_of)

FAIL = 0


def fail(msg):
    global FAIL
    FAIL += 1
    print(f"*** RANDOM FAILURE *** {msg}")


def random_bipartite(rng, n):
    n1 = rng.randint(1, n - 1)
    parts = list(range(n))
    rng.shuffle(parts)
    A, Bpart = parts[:n1], parts[n1:]
    q = rng.choice([0.15, 0.25, 0.35, 0.5])
    edges = [(min(a, b), max(a, b)) for a in A for b in Bpart
             if rng.random() < q]
    return sorted(set(edges))


def main():
    nlo, nhi, trials, seed = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    t0 = time.time()
    tested = rooted = 0
    for tr in range(trials):
        n = rng.randint(nlo, nhi)
        edges = random_bipartite(rng, n)
        if not edges:
            continue
        adj = adj_masks(n, edges)
        if any(x < 0 for x in bfs_dist(n, adj, 0)):
            continue
        dist = all_dists(n, edges)
        mcand = m_candidates(n, dist)
        if not mcand:
            continue
        bit = xor_bits(n)
        ebase = np.zeros(1 << n, dtype=np.int32)
        for a, b in edges:
            ebase += bit[a] ^ bit[b]
        # up to 8 random M-sets per graph
        for _ in range(8):
            k = rng.randint(1, min(4, len(mcand)))
            M = tuple(sorted(rng.sample(mcand, k)))
            if not union_triangle_free(n, edges, M):
                continue
            sl = ebase.copy()
            for e in M:
                sl -= bit[e[0]] ^ bit[e[1]]
            if sl.min() < 0:
                continue
            tested += 1
            ok = valid_stub_pairs(n, sl)
            gam = gamma_of(M, dist)
            for w in range(n):
                for x0 in range(n):
                    if not ok[w][x0]:
                        continue
                    rooted += 1
                    d = dist[w][x0]
                    s = n - 1 - d
                    if gam > rl_rhs(n, d):
                        fail(f"RL n={n} edges={edges} M={M} w={w} x0={x0}")
                    for (y, z) in M:
                        D = dist[y][z]
                        if D > 2 * s:
                            fail(f"SE1 n={n} edges={edges} M={M} w={w} "
                                 f"x0={x0} edge=({y},{z})")
                        if 2 * D > 2 * s + d:
                            fail(f"SE2 n={n} edges={edges} M={M} w={w} "
                                 f"x0={x0} edge=({y},{z})")
    print(f"trials={trials} M-sets tested={tested} rooted instances={rooted} "
          f"t={time.time()-t0:.0f}s FAILURES={FAIL}")
    sys.exit(1 if FAIL else 0)


if __name__ == "__main__":
    main()
