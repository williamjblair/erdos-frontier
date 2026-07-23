"""rl_inspect.py — decode and display a rooted one-stub witness in full:
adjacency, distances, geodesics, level structure from w, RL accounting.

Usage: python3 rl_inspect.py <g6> <M as 'a-b,c-d' or '-'> <w> <x0>
"""
import sys
from rl_lib import (parse_graph6, adj_masks, all_dists, p_of_d, rl_rhs,
                    gamma_of, geodesics_between, check_rfc_direct)


def main():
    g6, mstr, w, x0 = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    n, edges = parse_graph6(g6)
    M = []
    if mstr != "-":
        for part in mstr.split(","):
            a, b = part.split("-")
            M.append((int(a), int(b)))
    adj = adj_masks(n, edges)
    dist = all_dists(n, edges)
    ok, T = check_rfc_direct(n, edges, M, w, x0)
    d = dist[w][x0]
    s = n - 1 - d
    gam = gamma_of(M, dist)
    print(f"n={n} edges={edges}")
    print(f"M={M}  w={w}  x0={x0}   RFC valid: {ok}" +
          ("" if ok else f"  (violating T={T:0{n}b})"))
    print(f"d={d}  s={s}  p={p_of_d(d)}  Γ={gam}  rhs={rl_rhs(n, d)}  "
          f"slack={rl_rhs(n, d) - gam}")
    print(f"degrees: {[bin(adj[v]).count('1') for v in range(n)]}")
    print(f"levels from w: "
          f"{[[v for v in range(n) if dist[w][v] == i] for i in range(max(dist[w]) + 1)]}")
    print(f"stub geodesics w->x0: {geodesics_between(n, adj, dist, w, x0)}")
    for (a, b) in M:
        print(f"M-edge ({a},{b}) D={dist[a][b]}: geodesics "
              f"{geodesics_between(n, adj, dist, a, b)}")


if __name__ == "__main__":
    main()
