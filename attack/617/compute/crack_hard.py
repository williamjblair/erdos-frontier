#!/usr/bin/env python3
"""Recursive cube-and-conquer for the hard tail of a 617 leg.

Each input cube is a partial assignment (smsg 'a <lits> 0' line, or a
plain space-separated literal list) that survived a long flat solve.
We solve it with kissat under a per-node time budget; on timeout we
branch on a free variable into two children (var true / var false) and
recurse. Aggregation is sound:
  - every leaf UNSAT  => the cube is UNSAT
  - any leaf SAT      => the cube is SAT (raw witness dumped; must still
                         pass core.py ground truth)
Splitting is exponential difficulty reduction, so cubes that never
finish flat do finish once cut a few levels deep.

Usage:
  python3 crack_hard.py CNF HARDCUBES OUTDIR WORKERS [NODE_BUDGET_S] [MAXDEPTH]
HARDCUBES: one cube per line (leading 'a'/trailing '0' optional).
Results -> OUTDIR/crack_results.tsv  (cube_id  verdict  nodes  seconds)
Resume-aware: finished cube_ids in crack_results.tsv are skipped.
"""
import os, sys, subprocess, time, shutil
from concurrent.futures import ProcessPoolExecutor, as_completed

KISSAT = "./tools/kissat/build/kissat"
CNF, HARD, OUTDIR, WORKERS = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
NODE_BUDGET = int(sys.argv[5]) if len(sys.argv) > 5 else 600
MAXDEPTH = int(sys.argv[6]) if len(sys.argv) > 6 else 40
os.makedirs(OUTDIR, exist_ok=True)

with open(CNF) as f:
    hdr = f.readline().split()
    NV, NC = int(hdr[2]), int(hdr[3])
    BODY = f.read()  # clause lines, keep as-is

def parse_cube(line):
    toks = [t for t in line.split() if t not in ("a", "0", "")]
    return [int(t) for t in toks]

def kissat_solve(assump, node_id):
    """Solve CNF + unit assumptions. Return 'SAT'/'UNSAT'/'TIMEOUT'."""
    tmp = f"{OUTDIR}/n_{node_id}.cnf"
    with open(tmp, "w") as w:
        w.write(f"p cnf {NV} {NC + len(assump)}\n{BODY}")
        for l in assump:
            w.write(f"{l} 0\n")
    try:
        r = subprocess.run([KISSAT, "--quiet", f"--time={NODE_BUDGET}", tmp],
                           capture_output=True, text=True, timeout=NODE_BUDGET + 60)
        if r.returncode == 10:
            with open(f"{OUTDIR}/SAT_{node_id}.out", "w") as sf:
                sf.write(" ".join(map(str, assump)) + "\n" + r.stdout)
            return "SAT"
        if r.returncode == 20:
            return "UNSAT"
        return "TIMEOUT"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

def branch_var(assump):
    """Lowest-index variable not yet fixed by the assignment."""
    fixed = {abs(l) for l in assump}
    for v in range(1, NV + 1):
        if v not in fixed:
            return v
    return None

def crack(cube, cid):
    """Iterative DFS with an explicit stack; returns (verdict, nodes)."""
    stack = [(cube, 0)]
    nodes = 0
    while stack:
        assump, depth = stack.pop()
        nodes += 1
        v = kissat_solve(assump, f"{cid}_{nodes}")
        if v == "SAT":
            return "SAT", nodes
        if v == "UNSAT":
            continue  # this branch closed
        # TIMEOUT -> split
        if depth >= MAXDEPTH:
            return "MAXDEPTH", nodes
        bv = branch_var(assump)
        if bv is None:
            return "TIMEOUT-FULL", nodes  # fully assigned yet neither SAT/UNSAT: impossible, guard
        stack.append((assump + [bv], depth + 1))
        stack.append((assump + [-bv], depth + 1))
    return "UNSAT", nodes

def work(item):
    i, c = item
    t = time.time()
    verdict, nodes = crack(c, i)
    return i, verdict, nodes, time.time() - t

def main():
    cubes = [parse_cube(l) for l in open(HARD) if l.strip()]
    res_path = f"{OUTDIR}/crack_results.tsv"
    done = set()
    if os.path.exists(res_path):
        for line in open(res_path):
            p = line.split("\t")
            if len(p) >= 2 and p[1] in ("SAT", "UNSAT", "MAXDEPTH"):
                done.add(int(p[0]))
    todo = [(i, c) for i, c in enumerate(cubes) if i not in done]
    print(f"crack: {len(cubes)} hard cubes, {len(done)} done, {len(todo)} todo, "
          f"{WORKERS} workers, budget={NODE_BUDGET}s depth<={MAXDEPTH}", flush=True)

    sat = 0
    with ProcessPoolExecutor(max_workers=WORKERS) as ex, open(res_path, "a") as rf:
        futs = {ex.submit(work, it): it[0] for it in todo}
        n = len(done)
        for fut in as_completed(futs):
            i, verdict, nodes, dt = fut.result()
            rf.write(f"{i}\t{verdict}\t{nodes}\t{dt:.1f}\n"); rf.flush()
            n += 1
            if verdict == "SAT":
                sat += 1
                print(f"!!! SAT in hard cube {i} !!!", flush=True)
            print(f"[{n}/{len(cubes)}] cube {i}: {verdict} ({nodes} nodes, {dt:.0f}s)", flush=True)
    print(f"DONE: {len(cubes)} cubes, SAT={sat}", flush=True)

if __name__ == "__main__":
    main()
