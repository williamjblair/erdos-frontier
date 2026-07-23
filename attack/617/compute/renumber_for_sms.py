"""Renumber a K_25 leg DIMACS so class-0 edge vars occupy 1..300 in lex
edge order (SMS requirement: edge vars of the searched graph = 1..C(n,2)).

Pure variable renaming (bijection), semantics unchanged:
  x(k,0) = 5k+1  ->  k+1          (k = lex edge index, 0..299)
  every other var -> 301, 302, ... in increasing old-index order.

python3 renumber_for_sms.py runs/leg_sum_silent.cnf runs/sms_leg_sum_silent.cnf
"""
import sys


def main():
    src, dst = sys.argv[1], sys.argv[2]
    with open(src) as f:
        header = f.readline().split()
        nv, ncl = int(header[2]), int(header[3])
        mapping = {}
        for k in range(300):
            mapping[5 * k + 1] = k + 1
        nxt = 301
        for v in range(1, nv + 1):
            if v not in mapping:
                mapping[v] = nxt
                nxt += 1
        assert nxt - 1 == nv
        with open(dst, 'w') as g:
            g.write(f'p cnf {nv} {ncl}\n')
            for line in f:
                lits = line.split()
                out = []
                for tok in lits:
                    l = int(tok)
                    if l == 0:
                        break
                    out.append(mapping[abs(l)] if l > 0 else -mapping[abs(l)])
                g.write(' '.join(map(str, out)) + ' 0\n')
    print(f'{src} -> {dst} (renumbered, {nv} vars, {ncl} clauses)')


if __name__ == '__main__':
    main()
