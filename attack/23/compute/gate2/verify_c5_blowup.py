"""verify_c5_blowup.py — task-1 exact sanity checks for the Gamma-invariant.

Checks (all exact integer arithmetic, brute-force max cut where used):
  [1] C_5[q], q=1..4: the blow-up cut (V1 u V3 | V2 u V4 u V5) is a maximum cut,
      M = V4 x V5, every M-pair has d_B = 4, and Gamma = 25 q^2 = N^2 (equality).
  [2] C_5[1] and C_5[2]: enumerate ALL maximum cuts; report the multiset of
      Gamma values (equality-case census for the blow-up graphs themselves).
  [3] Odd cycles C_N, N = 5,7,9,11,13: every maximum cut gives Gamma = N^2.
  [4] Unbalanced blow-ups C_5[2,1,1,1,1], C_5[3,2,2,2,2], C_5[2,2,2,2,1]:
      every maximum cut gives Gamma < N^2 (strict).
  [5] C_7[2] (N=14): blow-up cut is max, Gamma = 196 = N^2 (equality beyond C_5).
  [6] Flip characterisation: on C_5[2]'s blow-up cut, for all T:
      e_M(delta T) <= e_B(delta T), and cut is max (cross-check of S2).
"""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from common import (all_max_cuts, max_cut_value, adj_masks, cut_value,
                    c5_blowup, cycle, blowup, gamma_of_instance,
                    is_triangle_free, flip_condition_holds, split_edges)

ok = True


def check(cond, msg):
    global ok
    print(("PASS " if cond else "FAIL ") + msg)
    if not cond:
        ok = False


# ---------------------------------------------------------------- [1] C_5[q]
for q in range(1, 5):
    n, edges, classes = c5_blowup([q] * 5)
    N = 5 * q
    assert n == N
    check(is_triangle_free(n, edges), f"C_5[{q}] triangle-free")
    # blow-up cut: classes 0 and 2 on side 1 (bitmask), rest side 0
    S = 0
    for v in classes[0] + classes[2]:
        S |= 1 << v
    adj = adj_masks(n, edges)
    cv = cut_value(n, adj, S)
    mc = max_cut_value(n, edges)
    check(cv == mc == 4 * q * q,
          f"C_5[{q}]: blow-up cut is max, mc = 4q^2 = {4*q*q}")
    inst = gamma_of_instance(n, edges, S)
    check(sorted(inst["dists"]) == [4] * (q * q),
          f"C_5[{q}]: |M| = q^2 = {q*q}, all d_B = 4")
    check(inst["Gamma"] == N * N,
          f"C_5[{q}]: Gamma = {inst['Gamma']} = N^2 = {N*N}  (EQUALITY)")

# ------------------------------------------------- [2] all max cuts, q = 1, 2
for q in (1, 2):
    n, edges, classes = c5_blowup([q] * 5)
    mc, cuts = all_max_cuts(n, edges)
    gams = []
    for S in cuts:
        inst = gamma_of_instance(n, edges, S)
        gams.append(inst["Gamma"])
    check(all(g == n * n for g in gams),
          f"C_5[{q}]: ALL {len(cuts)} max cuts have Gamma = N^2 "
          f"(values {sorted(set(gams))})")

# ------------------------------------------------------------ [3] odd cycles
for N in (5, 7, 9, 11, 13):
    n, edges = cycle(N)
    mc, cuts = all_max_cuts(n, edges)
    check(mc == N - 1, f"C_{N}: mc = N-1")
    gams = set()
    for S in cuts:
        inst = gamma_of_instance(n, edges, S)
        gams.add(inst["Gamma"])
    check(gams == {N * N},
          f"C_{N}: all {len(cuts)} max cuts give Gamma = N^2 = {N*N}  (EQUALITY)")

# ------------------------------------------- [4] unbalanced blow-ups (strict)
for sizes in ([2, 1, 1, 1, 1], [3, 2, 2, 2, 2], [2, 2, 2, 2, 1]):
    n, edges, classes = c5_blowup(sizes)
    mc, cuts = all_max_cuts(n, edges)
    worst = 0
    for S in cuts:
        inst = gamma_of_instance(n, edges, S)
        worst = max(worst, inst["Gamma"])
    check(worst < n * n,
          f"C_5{sizes}: max Gamma over all {len(cuts)} max cuts = {worst} "
          f"< N^2 = {n*n} (STRICT)")

# ----------------------------------------------------------------- [5] C_7[2]
n7, e7 = cycle(7)
n, edges, classes = blowup(7, e7, [2] * 7)
S = 0
for v in classes[0] + classes[2] + classes[4]:  # C_7 max cut leaves edge {5,6} mono
    S |= 1 << v
adj = adj_masks(n, edges)
cv = cut_value(n, adj, S)
mc = max_cut_value(n, edges)
check(cv == mc, f"C_7[2]: blow-up cut is a max cut (cut = {cv}, mc = {mc})")
inst = gamma_of_instance(n, edges, S)
check(inst["Gamma"] == n * n and sorted(inst["dists"]) == [6] * 4,
      f"C_7[2]: |M| = 4, all d_B = 6, Gamma = {inst['Gamma']} = N^2 = {n*n}"
      f"  (EQUALITY beyond C_5 blow-ups)")

# --------------------------------------------------- [6] flip characterisation
n, edges, classes = c5_blowup([2] * 5)
S = 0
for v in classes[0] + classes[2]:
    S |= 1 << v
holds, T = flip_condition_holds(n, edges, S)
check(holds, "C_5[2]: flip condition e_M(dT) <= e_B(dT) holds for ALL 2^9 T")

print()
print("ALL PASS" if ok else "SOME CHECKS FAILED")
sys.exit(0 if ok else 1)
