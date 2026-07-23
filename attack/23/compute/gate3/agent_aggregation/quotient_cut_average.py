"""Exact component-quotient cut averaging for a rooted corridor.

The theorem proved by :func:`quotient_cut_bound` is unconditional and uses
only RFC.  It is deliberately weaker than BF-RL: M-edges internal to one
component of ``B - V(P)`` are omitted.  It is useful because every remaining
M-edge is controlled simultaneously, without a multicommodity-routing or
per-vertex-load assertion.
"""

from __future__ import annotations

from dataclasses import dataclass

from compute23.gate2.common import adj_masks
from compute23.gate3.rl_lib import all_dists, check_rfc_direct


Edge = tuple[int, int]


def cut_count(edges: tuple[Edge, ...] | list[Edge], mask: int) -> int:
    return sum(((mask >> u) & 1) != ((mask >> v) & 1) for u, v in edges)


def off_components(
    n: int, b_edges: tuple[Edge, ...] | list[Edge], path: tuple[int, ...]
) -> tuple[tuple[int, ...], ...]:
    """Connected components of the induced graph on ``V - V(P)``."""

    path_set = set(path)
    adjacency = adj_masks(n, list(b_edges))
    unseen = set(range(n)) - path_set
    components: list[tuple[int, ...]] = []
    while unseen:
        start = min(unseen)
        stack = [start]
        unseen.remove(start)
        component = []
        while stack:
            u = stack.pop()
            component.append(u)
            neighbors = adjacency[u]
            while neighbors:
                v = (neighbors & -neighbors).bit_length() - 1
                neighbors &= neighbors - 1
                if v in unseen:
                    unseen.remove(v)
                    stack.append(v)
        components.append(tuple(sorted(component)))
    return tuple(components)


def assert_geodesic(
    n: int, b_edges: tuple[Edge, ...] | list[Edge], path: tuple[int, ...]
) -> None:
    assert len(path) >= 2 and len(set(path)) == len(path)
    edge_set = {tuple(sorted(e)) for e in b_edges}
    assert all(tuple(sorted((u, v))) in edge_set for u, v in zip(path, path[1:]))
    distances = all_dists(n, list(b_edges))
    assert distances[path[0]][path[-1]] == len(path) - 1


@dataclass(frozen=True)
class QuotientCutRecord:
    n: int
    d: int
    s: int
    component_sizes: tuple[int, ...]
    attachments: int
    mixed_m_edges: tuple[Edge, ...]
    path_internal_m_edges: tuple[Edge, ...]
    omitted_component_m_edges: tuple[Edge, ...]
    path_crossing_counts: tuple[int, ...]
    per_cut_margins: tuple[int, ...]
    summed_margin: int


def all_path_subset_margins(
    *,
    n: int,
    b_edges: tuple[Edge, ...] | list[Edge],
    m_edges: tuple[Edge, ...] | list[Edge],
    path: tuple[int, ...],
    reproduce_all_component_cuts: bool = False,
) -> tuple[int, ...]:
    """The stronger defect cut condition on every subset of path vertices.

    With the same ``A`` and ``M_mix`` as :func:`quotient_cut_bound`, every
    ``U subseteq V(P)`` satisfies

      |M_mix| + 2 e_{M[P]}(delta U) + 2 [U separates w,x0]
        <= A + 2 e_P(delta U).

    The suffix inequality is its specialization with both separation terms
    on the path equal to one.  The proof again sums symmetric RFC over all
    unions of ``U`` with whole off-corridor components.
    """

    b_edges = tuple(tuple(sorted(e)) for e in b_edges)
    m_edges = tuple(tuple(sorted(e)) for e in m_edges)
    assert_geodesic(n, b_edges, path)
    assert check_rfc_direct(n, list(b_edges), list(m_edges), path[0], path[-1]) == (
        True,
        None,
    )
    path_set = set(path)
    path_edges = tuple(tuple(sorted((u, v))) for u, v in zip(path, path[1:]))
    components = off_components(n, b_edges, path)
    component_of = {
        v: component_index
        for component_index, component in enumerate(components)
        for v in component
    }
    attachments = sum((u in path_set) != (v in path_set) for u, v in b_edges)
    mixed = []
    path_internal = []
    for edge in m_edges:
        u, v = edge
        u_on, v_on = u in path_set, v in path_set
        if u_on and v_on:
            path_internal.append(edge)
        elif not u_on and not v_on and component_of[u] == component_of[v]:
            pass
        else:
            mixed.append(edge)

    component_count = len(components)
    assert component_count >= 1
    assignment_count = 1 << component_count
    margins = []
    for path_choice in range(1 << len(path)):
        path_mask = sum(
            1 << vertex
            for index, vertex in enumerate(path)
            if (path_choice >> index) & 1
        )
        path_b_cut = cut_count(path_edges, path_mask)
        path_m_cut = cut_count(path_internal, path_mask)
        terminal_separation = ((path_choice >> 0) & 1) != (
            (path_choice >> (len(path) - 1)) & 1
        )
        margin = (
            attachments
            + 2 * path_b_cut
            - len(mixed)
            - 2 * path_m_cut
            - 2 * int(terminal_separation)
        )
        assert margin >= 0
        margins.append(margin)

        if reproduce_all_component_cuts:
            sum_b = sum_m = sum_terminal = 0
            for chosen in range(assignment_count):
                mask = path_mask
                for component_index, component in enumerate(components):
                    if (chosen >> component_index) & 1:
                        mask |= sum(1 << vertex for vertex in component)
                b_cut = cut_count(b_edges, mask)
                m_cut = cut_count(m_edges, mask)
                terminal = ((mask >> path[0]) & 1) != ((mask >> path[-1]) & 1)
                # Symmetric RFC; if the root lies in the displayed cut,
                # this is old RFC applied to its complement.
                assert m_cut + terminal <= b_cut
                sum_b += b_cut
                sum_m += m_cut
                sum_terminal += int(terminal)
            assert sum_b == assignment_count * path_b_cut + assignment_count * attachments // 2
            assert sum_m == assignment_count * path_m_cut + assignment_count * len(mixed) // 2
            assert sum_terminal == assignment_count * int(terminal_separation)
    return tuple(margins)


def quotient_cut_bound(
    *,
    n: int,
    b_edges: tuple[Edge, ...] | list[Edge],
    m_edges: tuple[Edge, ...] | list[Edge],
    path: tuple[int, ...],
    check_rfc: bool = True,
    reproduce_all_component_cuts: bool = False,
) -> QuotientCutRecord:
    """Verify and return the exact quotient-cut inequalities.

    ``path`` is a geodesic from the RFC root to its stub.  For every
    ``r=1,...,d``, let ``k_r`` count M-edges with both endpoints on ``P``
    whose path coordinates straddle the corridor cut.  Let ``M_mix`` be
    the M-edges which either join two distinct off-corridor components or
    join an off-corridor component to a path vertex.  Edges internal to one
    off-corridor component are explicitly omitted.  Then

        |M_mix| + 2 k_r <= A <= 2s,

    where ``A=e_B(V(P),V\\V(P))``.  Summing in ``r`` gives

        d |M_mix| + 2 sum_{uv in M[P]} d_B(u,v) <= d A.
    """

    b_edges = tuple(tuple(sorted(e)) for e in b_edges)
    m_edges = tuple(tuple(sorted(e)) for e in m_edges)
    assert_geodesic(n, b_edges, path)
    if check_rfc:
        assert check_rfc_direct(n, list(b_edges), list(m_edges), path[0], path[-1]) == (
            True,
            None,
        )

    d = len(path) - 1
    path_position = {v: i for i, v in enumerate(path)}
    path_set = set(path)
    components = off_components(n, b_edges, path)
    component_of = {
        v: component_index
        for component_index, component in enumerate(components)
        for v in component
    }

    attachments = sum((u in path_set) != (v in path_set) for u, v in b_edges)
    # Attachment lemma, checked here directly: two P-neighbors of an off-P
    # vertex have path coordinates differing by at most two and by even
    # parity, hence each off-P vertex has at most two P-neighbors.
    adjacency = adj_masks(n, list(b_edges))
    for v in range(n):
        if v in path_set:
            continue
        neighbors_on_path = [u for u in path if (adjacency[v] >> u) & 1]
        assert len(neighbors_on_path) <= 2
        if len(neighbors_on_path) == 2:
            i, j = sorted(path_position[u] for u in neighbors_on_path)
            assert j - i == 2
    s = n - len(path)
    assert attachments <= 2 * s

    mixed: list[Edge] = []
    path_internal: list[Edge] = []
    omitted: list[Edge] = []
    for edge in m_edges:
        u, v = edge
        u_on, v_on = u in path_set, v in path_set
        if u_on and v_on:
            path_internal.append(edge)
        elif not u_on and not v_on and component_of[u] == component_of[v]:
            omitted.append(edge)
        else:
            mixed.append(edge)

    crossing_counts: list[int] = []
    margins: list[int] = []
    component_count = len(components)
    assert component_count >= 1  # s>0 in every use of this averaging formula
    assignment_count = 1 << component_count
    for r in range(1, d + 1):
        k_r = sum(
            (path_position[u] < r <= path_position[v])
            or (path_position[v] < r <= path_position[u])
            for u, v in path_internal
        )
        crossing_counts.append(k_r)
        margin = attachments - len(mixed) - 2 * k_r
        assert margin >= 0
        margins.append(margin)

        if reproduce_all_component_cuts:
            sum_b = sum_m = 0
            suffix_mask = sum(1 << path[i] for i in range(r, d + 1))
            for chosen in range(assignment_count):
                mask = suffix_mask
                for component_index, component in enumerate(components):
                    if (chosen >> component_index) & 1:
                        mask |= sum(1 << v for v in component)
                b_cut = cut_count(b_edges, mask)
                m_cut = cut_count(m_edges, mask)
                # The root is outside, the stub inside, so RFC contributes
                # exactly one stub unit to every cut in the average.
                assert m_cut + 1 <= b_cut
                sum_b += b_cut
                sum_m += m_cut
            assert sum_b == assignment_count + assignment_count * attachments // 2
            assert sum_m == assignment_count * k_r + assignment_count * len(mixed) // 2

    distances = all_dists(n, list(b_edges))
    summed_left = d * len(mixed) + 2 * sum(
        distances[u][v] for u, v in path_internal
    )
    summed_margin = d * attachments - summed_left
    assert summed_margin == sum(margins)
    assert summed_margin >= 0
    return QuotientCutRecord(
        n=n,
        d=d,
        s=s,
        component_sizes=tuple(len(component) for component in components),
        attachments=attachments,
        mixed_m_edges=tuple(mixed),
        path_internal_m_edges=tuple(path_internal),
        omitted_component_m_edges=tuple(omitted),
        path_crossing_counts=tuple(crossing_counts),
        per_cut_margins=tuple(margins),
        summed_margin=summed_margin,
    )


def canonical_geodesic(
    n: int,
    b_edges: tuple[Edge, ...] | list[Edge],
    root: int,
    stub: int,
) -> tuple[int, ...]:
    """Lexicographically first shortest root--stub path."""

    distances = all_dists(n, list(b_edges))
    adjacency = adj_masks(n, list(b_edges))
    total = distances[root][stub]
    path = [root]
    while path[-1] != stub:
        u = path[-1]
        candidates = []
        neighbors = adjacency[u]
        while neighbors:
            v = (neighbors & -neighbors).bit_length() - 1
            neighbors &= neighbors - 1
            if (
                distances[root][v] == len(path)
                and distances[v][stub] == total - len(path)
            ):
                candidates.append(v)
        assert candidates
        path.append(min(candidates))
    return tuple(path)
