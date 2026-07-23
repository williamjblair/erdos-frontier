#!/usr/bin/env python3
"""Parallel cube solver: solve each cube of a leg via smsg --cube-line.

Verdict semantics (validated on SAT/UNSAT controls, cube-line mode):
  - smsg prints NO "Result:" line in cube mode
  - SAT   <=> a solution edge-list line "[(0,1),(0,2),...]" appears
  - UNSAT <=> "All cubes processed" with no solution line
Segfaulting/odd exits fall back to kissat on CNF + cube units, which is
sound: the raw CNF is a superset of the SMS-restricted space, so raw
UNSAT implies SMS UNSAT; raw SAT gives a candidate witness that must
pass core.py ground-truth verification regardless.

Resume-aware via results file. Usage:
  python3 cube_solver.py LEG CNF CUBEFILE OUTDIR WORKERS [SHARD NSHARDS]
SHARD/NSHARDS split the cube file across hosts: this instance solves
cube indexes i (1-based) with i % NSHARDS == SHARD. Results merge by
concatenating results.tsv files (cube index is globally unique).
"""
import re, shutil, subprocess, sys, os, time
from concurrent.futures import ProcessPoolExecutor, as_completed

SMSG = "./tools/sat-modulo-symmetries/build/src/smsg"
KISSAT = "./tools/kissat/build/kissat"
SOL_RE = re.compile(r"^\[\(\d+,\d+\)", re.M)
TIMEOUT = 3600
DONE_VERDICTS = ("SAT", "UNSAT", "SAT-k", "UNSAT-k")

leg, cnf, cubefile, outdir, workers = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
shard, nshards = (int(sys.argv[6]), int(sys.argv[7])) if len(sys.argv) > 7 else (0, 1)
os.makedirs(outdir, exist_ok=True)
cubes = open(cubefile).read().splitlines()
ncubes = len(cubes)
results_path = f"{outdir}/results.tsv"
done = set()
if os.path.exists(results_path):
    for line in open(results_path):
        p = line.split("\t")
        if len(p) >= 2 and p[1].strip() in DONE_VERDICTS:
            done.add(int(p[0]))
todo = [i for i in range(1, ncubes + 1) if i not in done and i % nshards == shard]
print(f"{leg}: {ncubes} cubes, {len(done)} done, {len(todo)} todo, {workers} workers", flush=True)


def cube_units(i):
    lits = cubes[i - 1].split()
    assert lits[0] == "a" and lits[-1] == "0"
    return lits[1:-1]


def kissat_fallback(i):
    tmp = f"{outdir}/tmp_cube_{i}.cnf"
    units = cube_units(i)
    with open(cnf) as src:
        header = src.readline().split()
        nv, nc = int(header[2]), int(header[3])
        with open(tmp, "w") as w:
            w.write(f"p cnf {nv} {nc + len(units)}\n")
            shutil.copyfileobj(src, w)
            for l in units:
                w.write(f"{l} 0\n")
    try:
        r = subprocess.run([KISSAT, "--quiet", tmp], capture_output=True, text=True, timeout=TIMEOUT)
        if r.returncode == 20:
            return "UNSAT-k"
        if r.returncode == 10:
            with open(f"{outdir}/sat_cube_{i}.out", "w") as wf:
                wf.write(r.stdout)
            return "SAT-k"
        return f"UNK2({r.returncode})"
    except subprocess.TimeoutExpired:
        return "TIMEOUT-k"
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)


def solve(i):
    t = time.time()
    try:
        r = subprocess.run([SMSG, "-v", "25", "--dimacs", cnf, "--cube-file", cubefile,
                            "--cube-line", str(i)], stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True, timeout=TIMEOUT)
        out = r.stdout
        if SOL_RE.search(out):
            with open(f"{outdir}/sat_cube_{i}.out", "w") as wf:
                wf.write(out)
            verdict = "SAT"
        elif "All cubes processed" in out:
            verdict = "UNSAT"
        else:
            verdict = kissat_fallback(i)
    except subprocess.TimeoutExpired:
        verdict = "TIMEOUT"
    return i, verdict, time.time() - t


sat_hits = 0
with ProcessPoolExecutor(max_workers=workers) as ex, open(results_path, "a") as rf:
    futs = {ex.submit(solve, i): i for i in todo}
    n = len(done)
    for fut in as_completed(futs):
        i, verdict, dt = fut.result()
        rf.write(f"{i}\t{verdict}\t{dt:.2f}\n"); rf.flush()
        n += 1
        if verdict.startswith("SAT"):
            sat_hits += 1
            print(f"!!! SAT CUBE {i} ({verdict}) !!!", flush=True)
        if n % 200 == 0:
            print(f"[{n}/{ncubes}] last={verdict} {dt:.1f}s", flush=True)
print(f"DONE {leg}: {n}/{ncubes}, SAT={sat_hits}", flush=True)
