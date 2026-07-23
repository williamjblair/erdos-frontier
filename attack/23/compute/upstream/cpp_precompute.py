#!/usr/bin/env python3
"""Compile + drive deficit_tensor.cpp (multithreaded C++ deficit-tensor precompute) and validate it
matches flag_cutgen.precompute_type. Enables higher-k (k=6,7) profile cuts that are infeasible in Python."""
import os, sys, struct, subprocess, tempfile, time
import numpy as np
import flag_engine as fe
import flag_cutgen as fc

HERE = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(HERE, "deficit_tensor.exe")
SRC = os.path.join(HERE, "deficit_tensor.cpp")

def compile_cpp():
    if os.path.exists(EXE) and os.path.getmtime(EXE) >= os.path.getmtime(SRC):
        return
    cmd = ["clang++", "-O3", "-std=c++17", "-march=native", SRC, "-o", EXE]
    print("  compiling:", " ".join(cmd), flush=True)
    subprocess.run(cmd, check=True)

def precompute_type_cpp(states, k, Asig, nthreads=32):
    classes = fc.profile_classes(k, Asig); nc = len(classes)
    cmask = [sum(1 << i for i in c) for c in classes]
    N = states[0][0]; ng = len(states)
    # Asig as k uint32 (Asig[a] bit b = edge a-b)
    asig = [int(Asig[a]) for a in range(k)]
    buf = bytearray()
    buf += struct.pack("<4i", N, k, nc, ng)
    buf += struct.pack("<%dI" % k, *asig)
    buf += struct.pack("<%dI" % nc, *cmask)
    for (n, A) in states:
        buf += struct.pack("<%dI" % N, *[int(A[u]) for u in range(N)])
    outf = os.path.join(tempfile.gettempdir(), f"dt_{os.getpid()}_{k}.bin")
    p = subprocess.run([EXE, outf, str(nthreads)], input=bytes(buf), stdout=subprocess.PIPE)
    with open(outf, "rb") as f:
        data = f.read()
    os.remove(outf)
    S = np.frombuffer(data[:8 * ng], dtype="<f8").copy()
    E = np.frombuffer(data[8 * ng:], dtype="<f8").reshape(ng, nc, nc).copy()
    # normalize to match precompute_type: E = Eraw/(nk*Cnmk2), S = Sraw/nk
    out_E = np.zeros((ng, nc, nc)); out_S = np.zeros(ng)
    for gi, (n, A) in enumerate(states):
        nk = 1
        for i in range(k):
            nk *= (n - i)
        nmk = n - k; Cnmk2 = nmk * (nmk - 1) / 2.0
        if nk == 0 or Cnmk2 <= 0:
            continue
        out_E[gi] = E[gi] / (nk * Cnmk2)
        out_S[gi] = S[gi] / nk
    return out_E, out_S, classes

EXE_M = os.path.join(HERE, "moment_tensor.exe")
SRC_M = os.path.join(HERE, "moment_tensor.cpp")

def compile_moment():
    if os.path.exists(EXE_M) and os.path.getmtime(EXE_M) >= os.path.getmtime(SRC_M):
        return
    cmd = ["clang++", "-O3", "-std=c++17", "-march=native", SRC_M, "-o", EXE_M]
    print("  compiling:", " ".join(cmd), flush=True); subprocess.run(cmd, check=True)

def _flag_key(m, A, k):
    def pk(perm):
        key = 0; bit = 0
        for i in range(m):
            for j in range(i + 1, m):
                if (A[perm[i]] >> perm[j]) & 1:
                    key |= (1 << bit)
                bit += 1
        return key
    p0 = list(range(m)); p1 = list(range(m)); p1[k], p1[k + 1] = p1[k + 1], p1[k]
    return min(pk(p0), pk(p1))

def precompute_moment_cpp(states, k, Asig, flags, nthreads=32):
    import flag_sdp as fs
    tt = len(flags); N = states[0][0]; ng = len(states)
    keybits = (k + 2) * (k + 1) // 2
    keymap = np.full(1 << keybits, -1, dtype="<i4")
    for idx, (fm, fA) in enumerate(flags):
        keymap[_flag_key(fm, fA, k)] = idx
    buf = bytearray()
    buf += struct.pack("<4i", N, k, tt, ng)
    buf += struct.pack("<%dI" % k, *[int(Asig[a]) for a in range(k)])
    buf += keymap.tobytes()
    for (n, A) in states:
        buf += struct.pack("<%dI" % N, *[int(A[u]) for u in range(N)])
    outf = os.path.join(tempfile.gettempdir(), f"mt_{os.getpid()}_{k}.bin")
    subprocess.run([EXE_M, outf, str(nthreads)], input=bytes(buf), stdout=subprocess.PIPE)
    with open(outf, "rb") as f:
        data = f.read()
    os.remove(outf)
    return np.frombuffer(data, dtype="<f8").reshape(ng, tt, tt).copy()

if __name__ == "__main__":
    compile_cpp(); compile_moment()
    import flag_sdp as fs
    st9 = fe.enumerate_graphs(9, triangle_free=True)
    print("validating C++ MOMENT vs Python P_sigma (order-9)...", flush=True)
    for nm, (k, A) in [("EDGE", (2, fe.adj_from_edges(2, [(0, 1)]))), ("C4", (4, fe.adj_from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)]))),
                       ("4K1", (4, [0, 0, 0, 0]))]:
        flags = fs.enumerate_flags((k, A), k + 2)
        t0 = time.time(); Mc = precompute_moment_cpp(st9, k, A, flags, 64); tc = time.time() - t0
        t0 = time.time(); Mp = fs.P_sigma(9, st9, (k, A), flags); tp = time.time() - t0
        Mp = np.array(Mp)
        print(f"  {nm} k={k} tt={len(flags)}: maxerr={np.abs(Mc-Mp).max():.2e} | cpp {tc:.2f}s vs py {tp:.1f}s ({tp/max(tc,1e-3):.0f}x)", flush=True)
    sys.exit(0)
    compile_cpp()
    states = fe.enumerate_graphs(9, triangle_free=True)
    print(f"validating C++ vs Python precompute_type (order-9, {len(states)} states)...", flush=True)
    for (k, A) in [(2, fe.adj_from_edges(2, [(0, 1)])), (2, [0, 0]),
                   (3, fe.adj_from_edges(3, [(0, 1), (1, 2)])), (4, fe.adj_from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])),
                   (5, fe.adj_from_edges(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]))]:
        t0 = time.time()
        Ec, Sc, cl = precompute_type_cpp(states, k, A, nthreads=32)
        tc = time.time() - t0
        t0 = time.time()
        Ep, Sp, _ = fc.precompute_type(states, k, A)
        tp = time.time() - t0
        eE = np.abs(Ec - Ep).max(); eS = np.abs(Sc - Sp).max()
        print(f"  k={k} nc={len(cl)}: maxerr E={eE:.2e} S={eS:.2e}  | cpp {tc:.2f}s vs py {tp:.2f}s ({tp/max(tc,1e-3):.0f}x)", flush=True)
    print("DONE", flush=True)
