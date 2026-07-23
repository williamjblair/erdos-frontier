"""Ground truth: max d_mono = 2(e - maxcut)/n^2 over triangle-free graphs with d_edge=e/C(n,2) in the
BCL medium band [0.2486,0.3197]. If sup < 0.08 -> a finite SDP can close (eta<0); if -> 0.08 -> tight
(no strict closure possible). Also report the max over ALL densities for context."""
import sys
import flag_engine as fe

def maxcut(n, A):
    adj = [[(A[u] >> v) & 1 for v in range(n)] for u in range(n)]
    best = 0
    for mask in range(1 << (n - 1)):
        side = [(mask >> u) & 1 for u in range(n)]
        cut = 0
        for u in range(n):
            su = side[u]
            for v in range(u + 1, n):
                if adj[u][v] and su != side[v]:
                    cut += 1
        if cut > best:
            best = cut
    return best

lo, hi = 0.2486, 0.3197
n0 = int(sys.argv[1]) if len(sys.argv) > 1 else 9
n1 = int(sys.argv[2]) if len(sys.argv) > 2 else 12
for n in range(n0, n1 + 1):
    C2 = n * (n - 1) // 2
    best_band = (-1.0, 0, 0, 0.0)
    best_all = (-1.0, 0, 0, 0.0)
    for (nn, A) in fe.enumerate_graphs(n, triangle_free=True):
        e = sum(1 for u in range(n) for v in range(u + 1, n) if (A[u] >> v) & 1)
        de = e / C2
        mc = maxcut(n, A)
        dm = 2 * (e - mc) / (n * n)
        if dm > best_all[0]:
            best_all = (dm, e, mc, de)
        if lo <= de <= hi and dm > best_band[0]:
            best_band = (dm, e, mc, de)
    print(f"n={n}: max d_mono IN BAND = {best_band[0]:.6f} (e={best_band[1]} maxcut={best_band[2]} d_edge={best_band[3]:.4f}) "
          f"| max d_mono ALL = {best_all[0]:.6f} (d_edge={best_all[3]:.4f})  [target 0.08]", flush=True)
print("DONE", flush=True)
