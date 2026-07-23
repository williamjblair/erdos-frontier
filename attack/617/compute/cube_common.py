"""Shared machinery for the cube-and-conquer campaign over the lemma legs.

Leg builders REPLICATE (by calling the same functions) the exact clause
lists of the running baseline instances:
  lemma_loud.py {silent, double_silent, floor_loud 1, edges_loud 5 75,
                 sum_silent}  and  silent_floor.py 75.
Expected clause counts (from the baseline logs, asserted here):
  silent 941,930 / double_silent 995,060 / floor_loud 1,526,432 /
  edges_loud 1,560,476 / sum_silent 1,370,770 / silent_floor75 230,230+card.

Cube semantics: a cube fixes the CLASS-0 indicator of every edge inside a
window W = {0..m-1} (for silent_floor75: the edge indicator itself).
Soundness of iso-reduced cube sets: every leg's constraint set is invariant
under the S_25 action pi: x_{e,c} -> x_{pi(e),c}, h_t -> h_{pi(t)},
H_{c,t} -> H_{c,pi(t)}, y_T -> y_{pi(T)} (cardinality constraints are
symmetric functions of their input literals; seqcounter aux vars are
re-extendable for any input assignment meeting the bound).  Hence for any
solution there is a relabeling supported on W mapping its W-pattern to the
canonical representative of its iso class: the formula is SAT iff some
canonical cube is SAT.  UNSAT of all canonical cubes => leg UNSAT.
"""
import json
import time
from itertools import combinations

import sys
sys.path.insert(0, '/Users/williamblair/personal/lean-proofs/compute617')

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

import lemma_loud as LL

E25 = LL.E25
EIDX25 = LL.EIDX25
xvar = LL.xvar


# ---------------------------------------------------------------- builders

def build_leg(leg):
    """Return (clauses, meta). meta: dict with decode info."""
    if leg == 'silent':
        cls = LL.base_validity()
        LL.silence(cls, 0)
        expect = 941930
        meta = {'kind': 'colored', 'hmap': None}
    elif leg == 'double_silent':
        cls = LL.base_validity()
        LL.silence(cls, 0)
        LL.silence(cls, 1)
        expect = 995060
        meta = {'kind': 'colored', 'hmap': None}
    elif leg == 'floor_loud':
        cls = LL.base_validity()
        LL.loudness(cls, 0)
        LL.admissibility(cls, 0)
        LL.hcard(cls, 1)
        expect = 1526432
        meta = {'kind': 'colored', 'hmap': {0: [LL.hvar(t) for t in range(25)]}}
    elif leg == 'edges_loud':
        cls = LL.base_validity()
        LL.loudness(cls, 0)
        LL.admissibility(cls, 0)
        top = LL.hcard(cls, 5)
        enc = CardEnc.atmost(lits=[xvar(k, 0) for k in range(300)],
                             bound=75, top_id=top + 10,
                             encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        expect = 1560476
        meta = {'kind': 'colored', 'hmap': {0: [LL.hvar(t) for t in range(25)]}}
    elif leg == 'sum_silent':
        cls = LL.base_validity()
        LL.silence(cls, 0)
        pool = IDPool(start_from=60000)
        hvs = {c: [pool.id(('H', c, t)) for t in range(25)]
               for c in range(1, 5)}
        for c in range(1, 5):
            for T in LL.FIVESETS:
                ks = [EIDX25[e] for e in combinations(T, 2)]
                cls.append([xvar(k, c) for k in ks] + [hvs[c][t] for t in T])
                cls.append([-xvar(k, c) for k in ks] + [-hvs[c][t] for t in T])
        enc = CardEnc.atmost(lits=[hvs[c][t] for c in range(1, 5)
                                   for t in range(25)],
                             bound=25, top_id=pool.top + 10,
                             encoding=EncType.seqcounter)
        cls.extend(enc.clauses)
        expect = 1370770
        meta = {'kind': 'colored', 'hmap': {c: hvs[c] for c in range(1, 5)}}
    elif leg == 'silent_floor75':
        base = []
        for T in combinations(range(25), 5):
            base.append([EIDX25[e] + 1 for e in combinations(T, 2)])
        for S in combinations(range(25), 6):
            base.append([-(EIDX25[e] + 1) for e in combinations(S, 2)])
        enc = CardEnc.atmost(lits=list(range(1, 301)), bound=75,
                             top_id=400, encoding=EncType.seqcounter)
        cls = base + enc.clauses
        expect = len(cls)          # baseline logged only 'base: 230230'
        assert len(base) == 230230, len(base)
        meta = {'kind': 'graph', 'hmap': None}
    else:
        raise ValueError(leg)
    assert len(cls) == expect, (leg, len(cls), expect)
    meta['leg'] = leg
    meta['nclauses'] = len(cls)
    return cls, meta


def cube_literals(leg_kind, m, edges):
    """Cube fixing the pattern on window {0..m-1}. edges: iterable of (u,v).
    Colored legs fix x_{e,0}; graph leg fixes the edge var."""
    es = set(tuple(sorted(e)) for e in edges)
    lits = []
    for e in combinations(range(m), 2):
        if leg_kind == 'graph':
            v = EIDX25[e] + 1
        else:
            v = xvar(EIDX25[e], 0)
        lits.append(v if e in es else -v)
    return lits


# ---------------------------------------------------------------- verify

def decode_coloring(model_set):
    col = []
    for k in range(300):
        cs = [c for c in range(5) if xvar(k, c) in model_set]
        assert len(cs) == 1, (k, cs)
        col.append(cs[0])
    return col


def class_masks(col, n=25):
    masks = [[0] * n for _ in range(5)]
    for k, c in enumerate(col):
        u, v = E25[k]
        masks[c][u] |= 1 << v
        masks[c][v] |= 1 << u
    return masks


def has_independent(adj, size, n=25):
    full = (1 << n) - 1

    def rec(chosen, cand):
        if chosen == size:
            return True
        if chosen + bin(cand).count('1') < size:
            return False
        c = cand
        while c:
            v = (c & -c).bit_length() - 1
            c &= c - 1
            if rec(chosen + 1, c & ~adj[v]):
                return True
        return False

    return rec(0, full)


def valid_k25(col):
    """Every 6-set sees all 5 colors <=> no class has an independent 6-set."""
    return all(not has_independent(adj, 6) for adj in class_masks(col))


def alpha_le(col, c, bound):
    return not has_independent(class_masks(col)[c], bound + 1)


def check_admissible(col, c, H):
    """H hits every independent 5-set of class c; no class-c 5-clique in H."""
    masks = class_masks(col)[c]
    Hs = set(H)
    for T in combinations(range(25), 5):
        indep = all(not (masks[u] >> v) & 1 for u, v in combinations(T, 2))
        if indep and not (set(T) & Hs):
            return False
        if set(T) <= Hs and all((masks[u] >> v) & 1
                                for u, v in combinations(T, 2)):
            return False
    return True


def extension_sat(col):
    """Exact 1-vertex extension of a valid K_25: partition V into admissible
    H_0..H_4.  Returns (True, k26_coloring) or (False, None)."""
    from pysat.solvers import Cadical195
    masks = class_masks(col)
    pvar = lambda v, c: 5 * v + c + 1
    cls = []
    for v in range(25):
        cls.append([pvar(v, c) for c in range(5)])
        for c, d in combinations(range(5), 2):
            cls.append([-pvar(v, c), -pvar(v, d)])
    for T in combinations(range(25), 5):
        pairs = list(combinations(T, 2))
        for c in range(5):
            adj = masks[c]
            ec = sum(1 for u, v in pairs if (adj[u] >> v) & 1)
            if ec == 0:                                  # independent in c
                cls.append([pvar(v, c) for v in T])
            elif ec == 10:                               # c-clique
                cls.append([-pvar(v, c) for v in T])
    with Cadical195(bootstrap_with=cls) as s:
        if not s.solve():
            return False, None
        m = set(l for l in s.get_model() if l > 0)
    # build K_26 coloring: vertices 0..24 + new vertex 25
    from core import EDGE_INDEX
    col26 = [None] * 325
    for k, c in enumerate(col):
        u, v = E25[k]
        col26[EDGE_INDEX[(u, v)]] = c
    for v in range(25):
        c = [c for c in range(5) if pvar(v, c) in m][0]
        col26[EDGE_INDEX[(v, 25)]] = c
    assert all(x is not None for x in col26)
    return True, col26


def verify_witness(leg, meta, model, outdir):
    """Full exact verification of a SAT cube model. Returns report dict."""
    import core
    mset = set(l for l in model if l > 0)
    rep = {'leg': leg, 'time': time.time()}
    if meta['kind'] == 'graph':
        g = [k for k in range(300) if (k + 1) in mset]
        adj = [0] * 25
        for k in g:
            u, v = E25[k]
            adj[u] |= 1 << v
            adj[v] |= 1 << u
        ok_alpha = not has_independent(adj, 5)
        ok_k6 = not all(False for _ in [0]) and not _has_clique(adj, 6)
        rep.update(nedges=len(g), alpha_le4=ok_alpha, k6free=ok_k6,
                   edges=[E25[k] for k in g],
                   verified=ok_alpha and ok_k6 and len(g) <= 75)
        _dump(rep, outdir, leg)
        return rep
    col = decode_coloring(mset)
    rep['coloring'] = col
    rep['valid_k25'] = valid_k25(col)
    if leg in ('silent', 'double_silent', 'sum_silent'):
        rep['class0_silent'] = alpha_le(col, 0, 4)
    if leg == 'double_silent':
        rep['class1_silent'] = alpha_le(col, 1, 4)
    if meta['hmap']:
        rep['H'] = {}
        for c, hv in meta['hmap'].items():
            H = [t for t in range(25) if hv[t] in mset]
            rep['H'][int(c)] = H
            rep[f'H{c}_admissible'] = check_admissible(col, int(c), H)
        rep['sumH'] = sum(len(v) for v in rep['H'].values())
    ext, col26 = extension_sat(col)
    rep['extension_sat'] = ext
    if ext:
        rep['k26_coloring'] = col26
        rep['is_counterexample'] = core.is_counterexample(col26)
        if rep['is_counterexample']:
            with open(f'{outdir}/witness.json', 'w') as f:
                json.dump(rep, f)
            print('\n' + '!' * 70)
            print('!!! K_26 COUNTEREXAMPLE VERIFIED BY core.is_counterexample'
                  ' — ERDOS 617 r=5 IS SAT !!!')
            print('!' * 70 + '\n', flush=True)
    _dump(rep, outdir, leg)
    return rep


def _has_clique(adj, size, n=25):
    comp = [((1 << n) - 1) & ~adj[v] & ~(1 << v) for v in range(n)]
    return has_independent(comp, size, n)


def _dump(rep, outdir, leg):
    import os
    os.makedirs(outdir, exist_ok=True)
    path = f'{outdir}/sat_witness_{leg}_{int(time.time())}.json'
    with open(path, 'w') as f:
        json.dump(rep, f)
    print(f'[witness saved: {path}]', flush=True)


def write_dimacs(cls, path, extra_units=()):
    nv = 0
    for c in cls:
        for l in c:
            if abs(l) > nv:
                nv = abs(l)
    with open(path, 'w') as f:
        f.write(f'p cnf {nv} {len(cls) + len(extra_units)}\n')
        for c in cls:
            f.write(' '.join(map(str, c)) + ' 0\n')
        for l in extra_units:
            f.write(f'{l} 0\n')
