"""Cube-and-conquer driver for one lemma leg.

Workers hold a PERSISTENT Cadical195 loaded once with the leg formula and
solve cubes as assumption sets under conflict budgets (learned clauses are
shared across cubes within a worker; zero re-parse cost).  Escalation:
pass k re-queues pass k-1's UNKNOWNs with the next budget.  Survivors of
the last pass are written to <outdir>/survivors.json for deepening or a
standalone-kissat uncapped stage.

Any SAT cube: full exact verification (valid K_25, leg side constraints,
1-vertex extension SAT; if extension holds, core.is_counterexample on the
K_26 coloring) and LOUD logging.  A verified-SAT leg stops the run.

Usage:
  python3 cube_run.py --leg sum_silent --cubes cubes/w7_colored.json \
      --outdir runs/cubes_sum_silent --workers 2 --budgets 100000,1000000

Scale up mid-run: echo N > <outdir>/workers.target
Restart-safe: cubes with a terminal verdict in results.tsv are skipped.
"""
import argparse
import json
import os
import sys
import time
import multiprocessing as mp

sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')


def log(outdir, msg):
    line = f'{time.strftime("%H:%M:%S")} {msg}'
    print(line, flush=True)
    with open(f'{outdir}/driver.log', 'a') as f:
        f.write(line + '\n')


def worker_main(leg, wid, inq, outq, outdir):
    os.nice(10)
    from pysat.solvers import Cadical195
    import cube_common as CC
    t0 = time.time()
    cls, meta = CC.build_leg(leg)
    outq.put(('built', wid, None, len(cls), time.time() - t0, None))
    solver = Cadical195(bootstrap_with=cls)
    del cls
    outq.put(('ready', wid, None, meta['nclauses'], time.time() - t0, None))
    while True:
        task = inq.get()
        if task is None:
            break
        cube_id, lits, budget, pass_no = task
        outq.put(('start', wid, cube_id, pass_no, budget, None))
        t = time.time()
        solver.conf_budget(budget)
        r = solver.solve_limited(assumptions=lits)
        wall = time.time() - t
        if r is True:
            model = solver.get_model()
            try:
                rep = CC.verify_witness(leg, meta, model, outdir)
                summary = {k: v for k, v in rep.items()
                           if k not in ('coloring', 'k26_coloring', 'edges',
                                        'H')}
            except Exception as e:
                summary = {'verify_error': repr(e)}
            outq.put(('done', wid, cube_id, pass_no,
                      ('SAT', wall, budget), summary))
        elif r is False:
            outq.put(('done', wid, cube_id, pass_no,
                      ('UNSAT', wall, budget), None))
        else:
            outq.put(('done', wid, cube_id, pass_no,
                      ('UNKNOWN', wall, budget), None))
    solver.delete()


def spawn(leg, wid, inq, outq, outdir):
    p = mp.Process(target=worker_main, args=(leg, wid, inq, outq, outdir),
                   daemon=True)
    p.start()
    return p


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--leg', required=True)
    ap.add_argument('--cubes', required=True)
    ap.add_argument('--outdir', required=True)
    ap.add_argument('--workers', type=int, default=2)
    ap.add_argument('--budgets', default='100000,1000000')
    args = ap.parse_args()
    os.makedirs(args.outdir, exist_ok=True)
    budgets = [int(b) for b in args.budgets.split(',')]

    cubes = json.load(open(args.cubes))
    done_ids = set()
    results_path = f'{args.outdir}/results.tsv'
    if os.path.exists(results_path):
        for line in open(results_path):
            p = line.rstrip('\n').split('\t')
            if len(p) >= 4 and p[3] in ('SAT', 'UNSAT'):
                done_ids.add(p[0])
    todo = [c for c in cubes if c['id'] not in done_ids]
    log(args.outdir, f'leg={args.leg} cubes={len(cubes)} '
        f'already-decided={len(done_ids)} todo={len(todo)} '
        f'budgets={budgets} workers={args.workers}')
    if not todo:
        log(args.outdir, 'nothing to do')
        return

    inq, outq = mp.Queue(), mp.Queue()
    workers = {}
    inflight = {}                     # wid -> task
    for w in range(args.workers):
        workers[w] = spawn(args.leg, w, inq, outq, args.outdir)

    res_f = open(results_path, 'a')

    def record(cube_id, pass_no, status, wall, budget, wid, summary):
        res_f.write(f'{cube_id}\t{pass_no}\t{budget}\t{status}\t{wall:.1f}\t'
                    f'w{wid}\t{json.dumps(summary) if summary else ""}\n')
        res_f.flush()

    pass_no = 0
    pending = {c['id']: c for c in todo}
    for c in todo:
        inq.put((c['id'], c['lits'], budgets[0], 0))
    counts = {'SAT': 0, 'UNSAT': 0, 'UNKNOWN': 0}
    unknowns = []
    last_status = time.time()
    total_this_pass = len(pending)
    done_this_pass = 0
    sat_seen = False
    t_start = time.time()
    slowest = (0.0, None)

    while True:
        # liveness + autoscale
        for wid, p in list(workers.items()):
            if not p.is_alive():
                t = inflight.pop(wid, None)
                if t is not None:
                    log(args.outdir, f'worker {wid} DIED with {t[0]}; '
                        f'requeueing + respawning')
                    inq.put(t)
                    nw = max(workers) + 1
                    workers[nw] = spawn(args.leg, nw, inq, outq, args.outdir)
                del workers[wid]
        tgt_path = f'{args.outdir}/workers.target'
        if os.path.exists(tgt_path):
            try:
                tgt = int(open(tgt_path).read().strip())
            except ValueError:
                tgt = len(workers)
            while tgt > len(workers):
                nw = (max(workers) + 1) if workers else 0
                workers[nw] = spawn(args.leg, nw, inq, outq, args.outdir)
                log(args.outdir, f'scaled up: worker {nw} spawned '
                    f'({len(workers)} total)')
        try:
            msg = outq.get(timeout=5)
        except Exception:
            msg = None
        if msg:
            kind, wid, cube_id, a, b, summary = msg
            if kind == 'built':
                log(args.outdir, f'worker {wid}: formula built '
                    f'({a} clauses, {b:.0f}s)')
            elif kind == 'ready':
                log(args.outdir, f'worker {wid}: solver loaded ({b:.0f}s)')
            elif kind == 'start':
                inflight[wid] = (cube_id, pending[cube_id]['lits'], b, a)
            elif kind == 'done':
                status, wall, budget = b
                inflight.pop(wid, None)
                counts[status] += 1
                done_this_pass += 1
                if wall > slowest[0]:
                    slowest = (wall, cube_id)
                record(cube_id, a, status, wall, budget, wid, summary)
                if status == 'SAT':
                    sat_seen = True
                    log(args.outdir, '=' * 60)
                    log(args.outdir, f'*** SAT CUBE {cube_id} on leg '
                        f'{args.leg} (wall {wall:.1f}s) ***')
                    log(args.outdir, f'*** verification summary: '
                        f'{json.dumps(summary)} ***')
                    log(args.outdir, '=' * 60)
                elif status == 'UNKNOWN':
                    unknowns.append(pending[cube_id])
        if sat_seen:
            log(args.outdir, f'LEG {args.leg}: SAT — stopping (see witness '
                f'json + summary above). counts={counts}')
            break
        if time.time() - last_status > 60:
            last_status = time.time()
            log(args.outdir, f'pass {pass_no} [{done_this_pass}/'
                f'{total_this_pass}] counts={counts} '
                f'slowest={slowest[0]:.0f}s@{slowest[1]} '
                f'workers={len(workers)} elapsed={time.time()-t_start:.0f}s')
        if done_this_pass >= total_this_pass:
            log(args.outdir, f'pass {pass_no} complete: counts={counts} '
                f'unknowns={len(unknowns)}')
            if not unknowns:
                log(args.outdir, f'LEG {args.leg}: ALL CUBES UNSAT — leg '
                    f'DECIDED (UNSAT modulo iso-cube covering argument, '
                    f'see cube_common.py docstring).')
                break
            pass_no += 1
            if pass_no >= len(budgets):
                with open(f'{args.outdir}/survivors.json', 'w') as f:
                    json.dump(unknowns, f)
                log(args.outdir, f'passes exhausted; {len(unknowns)} '
                    f'survivors -> survivors.json (deepen or kissat them)')
                break
            total_this_pass = len(unknowns)
            done_this_pass = 0
            for c in unknowns:
                inq.put((c['id'], c['lits'], budgets[pass_no], pass_no))
            log(args.outdir, f'pass {pass_no} started: '
                f'{total_this_pass} cubes at budget {budgets[pass_no]}')
            unknowns = []
            slowest = (0.0, None)
    for _ in workers:
        inq.put(None)
    time.sleep(2)
    for p in workers.values():
        if p.is_alive():
            p.terminate()
    res_f.close()
    log(args.outdir, f'driver exit. total wall {time.time()-t_start:.0f}s')


if __name__ == '__main__':
    mp.set_start_method('spawn')
    main()
