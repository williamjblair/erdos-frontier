#!/usr/bin/env python3
"""
Flag-algebra SDP assembly (Stage 3-4), on top of flag_engine.
- enumerate_flags(sigma, m): triangle-free sigma-flags on m vertices up to root-fixing iso.
- P_sigma(N, states, sigma, flags): for each order-N state H, the t x t matrix of flag-product
  coefficients   P^sigma_ij(H) = #{ ordered k-tuple R + disjoint s-subsets S1,S2 in H :
                    R induces sigma (in order), (R,S1)=F_i, (R,S2)=F_j }   (raw count; uniform
  normalization absorbed into the PSD multiplier Q).
- solve_flag_sdp(...): minimize c s.t. for every triangle-free state H,
     obj(H) + sum_sigma <Q_sigma, P^sigma(H)> <= c,   Q_sigma PSD.
  Returns the bound c (an UPPER bound on max_H-graphon obj).

Validation target (Phase B): Mantel — max edge density among triangle-free graphs = 1/2.
"""
import itertools
import numpy as np
import cvxpy as cp
import flag_engine as fe


# ---------- sigma-flags ----------
def root_canonical(m, A, k):
    return fe.canonical(m, A, roots=k)

def enumerate_flags(sigma, m, triangle_free=True):
    """All triangle-free sigma-flags on m vertices up to root-fixing iso.
    sigma=(k,Asig): the first k vertices must induce sigma EXACTLY (labeled)."""
    k, Asig = sigma
    assert m >= k
    # free-edge slots: (root i < k, free j>=k) and (free i<j, both>=k)
    slots = [(i, j) for i in range(k) for j in range(k, m)] + \
            [(i, j) for i in range(k, m) for j in range(i+1, m)]
    seen = {}
    for bits in itertools.product((0, 1), repeat=len(slots)):
        A = [0]*m
        # roots induce sigma
        for i in range(k):
            for j in range(i+1, k):
                if (Asig[i] >> j) & 1:
                    A[i] |= 1 << j; A[j] |= 1 << i
        for (slot, b) in zip(slots, bits):
            if b:
                i, j = slot; A[i] |= 1 << j; A[j] |= 1 << i
        if triangle_free and not fe.is_triangle_free(m, A):
            continue
        ck = root_canonical(m, A, k)
        if ck not in seen:
            seen[ck] = (m, fe.graph_from_key(m, ck))
    return list(seen.values())


def _induces_sigma_ordered(Ah, R, sigma):
    """Does the ordered tuple R induce sigma EXACTLY (as labeled graph) in Ah?"""
    k, Asig = sigma
    for a in range(k):
        for b in range(a+1, k):
            e = 1 if (Ah[R[a]] >> R[b]) & 1 else 0
            s = 1 if (Asig[a] >> b) & 1 else 0
            if e != s:
                return False
    return True


def _flag_key_of(Ah, R, S, k):
    """Root-canonical key of the sigma-flag with roots R (ordered) and free set S (unordered)."""
    verts = list(R) + list(S)
    m = len(verts)
    _, B = fe.induced(Ah, verts)   # roots first (0..k-1), then free
    return fe.canonical(m, B, roots=k)


def P_sigma(N, states, sigma, flags):
    """Return list (over states) of t x t numpy matrices P^sigma(H) (raw counts)."""
    k, Asig = sigma
    s = flags[0][0] - k          # free size
    t = len(flags)
    flagkey = {root_canonical(fm, fA, k): idx for idx, (fm, fA) in enumerate(flags)}
    mats = []
    for (n, Ah) in states:
        M = np.zeros((t, t))
        rest_all = list(range(n))
        for R in itertools.permutations(range(n), k):
            if not _induces_sigma_ordered(Ah, R, sigma):
                continue
            rest = [v for v in rest_all if v not in R]
            subs = list(itertools.combinations(rest, s))
            # precompute flag index for each candidate free-set
            idxs = []
            for S in subs:
                key = _flag_key_of(Ah, R, S, k)
                idxs.append(flagkey.get(key, -1))
            for a in range(len(subs)):
                ia = idxs[a]
                if ia < 0: continue
                Sa = set(subs[a])
                for b in range(len(subs)):
                    ib = idxs[b]
                    if ib < 0: continue
                    if Sa & set(subs[b]): continue   # S1, S2 must be disjoint
                    M[ia, ib] += 1.0
        mats.append(M)
    return mats


def edge_density(states):
    edge = (2, fe.adj_from_edges(2, [(0, 1)]))
    return np.array([fe.induced_density(edge, H) for H in states])


def solve_flag_sdp(N, obj_vec, types_and_flags, triangle_free=True, sense="max", solver=cp.CLARABEL):
    """minimize c s.t. for all states H: obj(H) + sum_sigma <Q_sigma, P^sigma(H)> <= c (sense=max).
       For sense='min' (lower bound) we maximize c with >=. Returns (bound, status)."""
    states = fe.enumerate_graphs(N, triangle_free=triangle_free)
    Pmats = []
    for (sigma, flags) in types_and_flags:
        Pmats.append((P_sigma(N, states, sigma, flags), len(flags)))
    c = cp.Variable()
    Qs = [cp.Variable((t, t), symmetric=True) for (_, t) in Pmats]
    cons = [Q >> 0 for Q in Qs]
    for hi, H in enumerate(states):
        expr = obj_vec[hi]
        for (mats, t), Q in zip(Pmats, Qs):
            expr = expr + cp.sum(cp.multiply(Q, mats[hi]))
        if sense == "max":
            cons.append(expr <= c)
        else:
            cons.append(expr >= c)
    prob = cp.Problem(cp.Minimize(c) if sense == "max" else cp.Maximize(c), cons)
    prob.solve(solver=solver)
    return float(c.value), prob.status, states


if __name__ == "__main__":
    print("=== Phase B validation: Mantel (max triangle-free edge density = 1/2) ===")
    # type = single labeled vertex (K1); flags of order 2 (s=1)
    K1 = (1, [0])
    flags1 = enumerate_flags(K1, 2)
    print(f"  K1-type order-2 flags: {len(flags1)} (expect 2: isolated / pendant)")
    for N in (3, 4, 5):
        states = fe.enumerate_graphs(N, True)
        obj = edge_density(states)
        tf = [(K1, enumerate_flags(K1, 2))]
        # for N>=5 also add edge-type with order-3 flags (s=1) for tightness
        bound, status, _ = solve_flag_sdp(N, obj, tf, sense="max")
        print(f"  N={N}: flag-SDP upper bound on edge density = {bound:.6f}  (Mantel=0.5)  status={status}")
    print("DONE")
