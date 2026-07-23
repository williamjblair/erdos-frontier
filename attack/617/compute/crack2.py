#!/usr/bin/env python3
"""Structural cube-and-conquer for the hard tail of a 617 leg.

Splits a hard cube with smsg's OWN edge-variable cutoff (the heuristic
that made the coarse cubes tractable), not naive variable branching.

Node = a set of assumption literals over the base CNF.
  solve(node): kissat(base + node units) with a time budget.
    SAT   -> witness dumped, propagate up
    UNSAT -> branch closed
    TIMEOUT -> split: run smsg --simple-assignment-cutoff (deeper than the
      node's depth) on base+node, take each emitted 'a .. 0' cube, union
      with node units -> children; recurse. Deeper cutoff => structurally
      easier leaves.
Sound aggregation: all leaves UNSAT => node UNSAT; any leaf SAT => SAT.

Usage:
  python3 crack2.py CNF HARDCUBES OUTDIR WORKERS [LEAF_BUDGET_S] [CUT0] [CUTSTEP] [MAXCUT]
Results -> OUTDIR/crack_results.tsv  (cube_id verdict leaves seconds)
Resume-aware on cube_id.
"""
import os, sys, subprocess, time
from concurrent.futures import ProcessPoolExecutor, as_completed

SMSG = "./tools/sat-modulo-symmetries/build/src/smsg"
KISSAT = "./tools/kissat/build/kissat"
CNF, HARD, OUTDIR, WORKERS = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
LEAF_BUDGET = int(sys.argv[5]) if len(sys.argv) > 5 else 900
CUT0 = int(sys.argv[6]) if len(sys.argv) > 6 else 110
CUTSTEP = int(sys.argv[7]) if len(sys.argv) > 7 else 40
MAXCUT = int(sys.argv[8]) if len(sys.argv) > 8 else 290
os.makedirs(OUTDIR, exist_ok=True)

with open(CNF) as f:
    hdr = f.readline().split()
    NV, NC = int(hdr[2]), int(hdr[3])
    BODY = f.read()

def parse_cube(line):
    return [int(t) for t in line.split() if t not in ("a", "0", "")]

def restricted_cnf(units, tag):
    p = f"{OUTDIR}/r_{tag}.cnf"
    with open(p, "w") as w:
        w.write(f"p cnf {NV} {NC + len(units)}\n{BODY}")
        for l in units:
            w.write(f"{l} 0\n")
    return p

def kissat_solve(units, tag):
    p = restricted_cnf(units, tag)
    try:
        r = subprocess.run([KISSAT, "--quiet", f"--time={LEAF_BUDGET}", p],
                           capture_output=True, text=True, timeout=LEAF_BUDGET + 60)
        if r.returncode == 10:
            with open(f"{OUTDIR}/SAT_{tag}.out", "w") as sf:
                sf.write(" ".join(map(str, units)) + "\n" + r.stdout)
            return "SAT"
        if r.returncode == 20:
            return "UNSAT"
        return "TIMEOUT"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    finally:
        if os.path.exists(p):
            os.unlink(p)

def gen_subcubes(units, cutoff, tag):
    """Structural split: smsg edge-var cubing on base+units at `cutoff`."""
    p = restricted_cnf(units, f"g{tag}")
    try:
        r = subprocess.run([SMSG, "-v", "25", "--dimacs", p,
                            "--simple-assignment-cutoff", str(cutoff)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                           text=True, timeout=1800)
        subs = [parse_cube(l) for l in r.stdout.splitlines() if l.startswith("a ")]
        return subs
    except subprocess.TimeoutExpired:
        return []
    finally:
        if os.path.exists(p):
            os.unlink(p)

LONG_BUDGET = 7200  # escalation for maximally-constrained terminal leaves

def solve_long(units, tag):
    """Unbounded-ish kissat on a leaf that can no longer be split."""
    p = restricted_cnf(units, f"L{tag}")
    try:
        r = subprocess.run([KISSAT, "--quiet", f"--time={LONG_BUDGET}", p],
                           capture_output=True, text=True, timeout=LONG_BUDGET + 120)
        if r.returncode == 10:
            with open(f"{OUTDIR}/SAT_{tag}.out", "w") as sf:
                sf.write(" ".join(map(str, units)) + "\n" + r.stdout)
            return "SAT"
        if r.returncode == 20:
            return "UNSAT"
        return "TIMEOUT"
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    finally:
        if os.path.exists(p):
            os.unlink(p)

def crack(cube, cid):
    # stack of (units, cutoff_for_next_split)
    stack = [(list(cube), CUT0)]
    leaves = 0
    while stack:
        units, cutoff = stack.pop()
        leaves += 1
        v = kissat_solve(units, f"{cid}_{leaves}")
        if v == "SAT":
            return "SAT", leaves
        if v == "UNSAT":
            continue
        # TIMEOUT -> try structural split first
        subs = [] if cutoff > MAXCUT else gen_subcubes(units, cutoff, f"{cid}_{leaves}")
        if subs:
            seen = set(units)
            for s in subs:
                child = units + [l for l in s if l not in seen and -l not in seen]
                stack.append((child, cutoff + CUTSTEP))
            continue
        # cannot split further (edge vars exhausted / past max) -> escalate budget
        vl = solve_long(units, f"{cid}_{leaves}")
        if vl == "SAT":
            return "SAT", leaves
        if vl == "UNSAT":
            continue
        return "STUCK", leaves  # genuinely hard even fully constrained + 2h solve
    return "UNSAT", leaves

def work(item):
    i, c = item
    t = time.time()
    verdict, leaves = crack(c, i)
    return i, verdict, leaves, time.time() - t

def main():
    cubes = [parse_cube(l) for l in open(HARD) if l.strip()]
    res_path = f"{OUTDIR}/crack_results.tsv"
    done = set()
    if os.path.exists(res_path):
        for line in open(res_path):
            p = line.split("\t")
            if len(p) >= 2 and p[1] in ("SAT", "UNSAT", "MAXCUT", "GENFAIL"):
                done.add(int(p[0]))
    todo = [(i, c) for i, c in enumerate(cubes) if i not in done]
    print(f"crack2: {len(cubes)} cubes, {len(done)} done, {len(todo)} todo, {WORKERS}w, "
          f"leaf={LEAF_BUDGET}s cut {CUT0}->{MAXCUT} step {CUTSTEP}", flush=True)
    sat = 0
    with ProcessPoolExecutor(max_workers=WORKERS) as ex, open(res_path, "a") as rf:
        futs = {ex.submit(work, it): it[0] for it in todo}
        n = len(done)
        for fut in as_completed(futs):
            i, verdict, leaves, dt = fut.result()
            rf.write(f"{i}\t{verdict}\t{leaves}\t{dt:.1f}\n"); rf.flush()
            n += 1
            if verdict == "SAT":
                sat += 1
                print(f"!!! SAT in hard cube {i} !!!", flush=True)
            print(f"[{n}/{len(cubes)}] cube {i}: {verdict} ({leaves} leaves, {dt:.0f}s)", flush=True)
    print(f"DONE: SAT={sat}", flush=True)

if __name__ == "__main__":
    main()
