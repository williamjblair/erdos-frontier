"""Independent hostile verifier for the Erdős #23 G-B series route.

This file intentionally imports neither the producer verifier nor `rl_lib`.
It reimplements graph distances, cut counts, rooted validity, triangle
checking, bridge components, partner distance, and the RL budget directly.
All calculations use Python integers.
"""

from __future__ import annotations

from collections import deque
from itertools import product


def _p(d: int) -> int:
    assert d >= 1
    if d == 1:
        return 3
    if (d & 1) == 0:
        return 2
    return 1


def _budget(s: int, d: int) -> int:
    assert s >= 0 and d >= 1
    return s * (s + 2 * d + 2 + 2 * _p(d))


def _sep(a: int, b: int) -> int:
    return a ^ b


def _cut(edges: tuple[tuple[int, int], ...], mask: int) -> int:
    total = 0
    for a, b in edges:
        total += ((mask >> a) ^ (mask >> b)) & 1
    return total


def _adj(n: int, edges: tuple[tuple[int, int], ...], omit=None):
    out = [set() for _ in range(n)]
    for a, b in edges:
        if omit is not None and {a, b} == set(omit):
            continue
        out[a].add(b)
        out[b].add(a)
    return out


def _distances(n: int, edges: tuple[tuple[int, int], ...]):
    adj = _adj(n, edges)
    ans = []
    for source in range(n):
        dist = [-1] * n
        dist[source] = 0
        q = deque([source])
        while q:
            u = q.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1
                    q.append(v)
        ans.append(dist)
    return ans


def _component(n: int, edges: tuple[tuple[int, int], ...], source: int, omit):
    adj = _adj(n, edges, omit=omit)
    seen = {source}
    q = deque([source])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                q.append(v)
    return seen


def _is_bipartite_connected(n: int, edges: tuple[tuple[int, int], ...]) -> bool:
    adj = _adj(n, edges)
    colour = [None] * n
    colour[0] = 0
    q = deque([0])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if colour[v] is None:
                colour[v] = 1 - colour[u]
                q.append(v)
            elif colour[v] == colour[u]:
                return False
    return all(c is not None for c in colour)


def _is_triangle_free(n: int, edges: tuple[tuple[int, int], ...]) -> bool:
    adj = _adj(n, edges)
    for a in range(n):
        for b in adj[a]:
            if b <= a:
                continue
            if adj[a] & adj[b]:
                return False
    return True


def _fixture():
    block = (
        (0, 4),
        (1, 4),
        (2, 5),
        (3, 5),
        (0, 6),
        (1, 6),
        (2, 6),
        (3, 6),
    )
    block2 = tuple((a + 7, b + 7) for a, b in block)
    B = block + block2 + ((5, 11),)
    M = ((4, 5), (11, 12))
    return block, block2, B, M


def _mixed_fixture():
    short, _, _, _ = _fixture()
    long_base = (
        (0, 6),
        (1, 6),
        (2, 7),
        (3, 7),
        (0, 8),
        (1, 8),
        (4, 8),
        (5, 8),
        (2, 9),
        (3, 9),
        (4, 9),
        (5, 9),
    )
    long = tuple((a + 7, b + 7) for a, b in long_base)
    B = short + long + ((5, 13),)
    M = ((4, 5), (13, 14))
    return B, M


def hostile_audit():
    # The cutwise terminal inequality is checked independently on its entire
    # Boolean domain, including every orientation of the bridge cut.
    terminal_cases = 0
    for a, b, c, d in product((0, 1), repeat=4):
        assert _sep(a, d) <= _sep(a, b) + _sep(b, c) + _sep(c, d)
        terminal_cases += 1

    block1, block2, B, M = _fixture()
    n = 14
    bridge = (5, 11)
    assert _is_bipartite_connected(n, B)
    assert _is_triangle_free(n, B + M)
    left = _component(n, B, 4, bridge)
    right = _component(n, B, 12, bridge)
    assert left == set(range(7))
    assert right == set(range(7, 14))
    assert left.isdisjoint(right) and left | right == set(range(n))

    # Symmetric rooted cut conditions, independently checked on every cut.
    global_min = None
    for mask in range(1 << n):
        bit = lambda v: (mask >> v) & 1
        b1, b2 = _cut(block1, mask), _cut(block2, mask)
        m1 = _cut((M[0],), mask)
        m2 = _cut((M[1],), mask)
        q1 = _sep(bit(4), bit(5))
        q2 = _sep(bit(11), bit(12))
        eb = _sep(bit(5), bit(11))
        q = _sep(bit(4), bit(12))
        assert m1 + q1 <= b1
        assert m2 + q2 <= b2
        assert _cut(B, mask) == b1 + b2 + eb
        assert _cut(M, mask) == m1 + m2
        assert q <= q1 + eb + q2
        slack = _cut(B, mask) - _cut(M, mask) - q
        assert slack >= 0
        global_min = slack if global_min is None else min(global_min, slack)
    assert global_min == 0

    dist = _distances(n, B)
    assert all(x >= 0 for row in dist for x in row)
    assert [dist[a][b] for a, b in M] == [4, 4]
    d = dist[4][12]
    s = n - 1 - d
    gamma = sum((dist[a][b] + 1) ** 2 for a, b in M)
    assert (d, s, gamma) == (9, 4, 50)
    assert 2 * s * _p(d) < (d + 1) ** 2
    assert _budget(s, d) == 104
    assert gamma <= _budget(s, d)
    assert _budget(2, 4) == 32

    # Mixed-distance falsification boundary: the same theorem must tolerate
    # D=4 and D=6 simultaneously, with no constant-distance assumption.
    mixed_B, mixed_M = _mixed_fixture()
    mixed_n = 17
    assert _is_bipartite_connected(mixed_n, mixed_B)
    assert _is_triangle_free(mixed_n, mixed_B + mixed_M)
    mixed_left = _component(mixed_n, mixed_B, 4, (5, 13))
    mixed_right = _component(mixed_n, mixed_B, 14, (5, 13))
    assert (len(mixed_left), len(mixed_right)) == (7, 10)
    mixed_dist = _distances(mixed_n, mixed_B)
    mixed_Ds = tuple(mixed_dist[a][b] for a, b in mixed_M)
    mixed_d = mixed_dist[4][14]
    mixed_s = mixed_n - 1 - mixed_d
    mixed_gamma = sum((mixed_dist[a][b] + 1) ** 2 for a, b in mixed_M)
    assert (mixed_Ds, mixed_d, mixed_s, mixed_gamma) == ((4, 6), 11, 5, 74)
    assert 2 * mixed_s * _p(mixed_d) < (mixed_d + 1) ** 2
    for mask in range(1 << mixed_n):
        q = _sep((mask >> 4) & 1, (mask >> 14) & 1)
        assert _cut(mixed_M, mask) + q <= _cut(mixed_B, mask)

    # Hostile arithmetic box: every positive distance, both zero and nonzero
    # slacks, all parity transitions, and over five million exact cases.
    arithmetic_cases = 0
    minimum_margin = None
    for d1 in range(1, 97):
        for d2 in range(1, 97):
            D = d1 + d2 + 1
            P = _p(D)
            assert 1 <= P <= 3
            assert _p(d1) <= d2 + 1 + P
            assert _p(d2) <= d1 + 1 + P
            for s1 in range(25):
                for s2 in range(25):
                    margin = _budget(s1 + s2, D) - _budget(s1, d1) - _budget(s2, d2)
                    factored = (
                        2 * s1 * (s2 + d2 + 1 + P - _p(d1))
                        + 2 * s2 * (d1 + 1 + P - _p(d2))
                    )
                    assert margin == factored
                    assert margin >= 0
                    minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
                    arithmetic_cases += 1

    return {
        "verdict": "PASS",
        "terminal_assignments": terminal_cases,
        "fixture_cuts": 1 << n,
        "fixture_tuple": (n, len(M), d, s, gamma, _budget(s, d)),
        "bridge_component_sizes": (len(left), len(right)),
        "mixed_fixture_tuple": (
            mixed_n,
            len(mixed_M),
            mixed_d,
            mixed_s,
            mixed_gamma,
            _budget(mixed_s, mixed_d),
        ),
        "mixed_distances": mixed_Ds,
        "arithmetic_cases": arithmetic_cases,
        "minimum_margin": minimum_margin,
    }


if __name__ == "__main__":
    print(hostile_audit())
