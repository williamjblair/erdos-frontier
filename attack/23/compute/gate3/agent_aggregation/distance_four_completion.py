"""Exact shared-path completion for a distance-four demand graph.

The construction takes a supplied proper edge coloring of the (triangle-free)
demand graph.  It uses one endpoint and one port per demand endpoint and one
center per used edge color.  A demand ``uv`` of color ``c`` receives the
four-edge supply path

    u -- port(v) -- center(c) -- port(u) -- v.

Proper edge coloring makes these paths edge-disjoint.  Triangle-freeness of
the demand graph says adjacent demand endpoints have no common demand
neighbor, so their supply distance is not two; bipartiteness then makes the
displayed distance exactly four.
"""

from __future__ import annotations

from dataclasses import dataclass

from compute23.gate2.common import adj_masks
from compute23.gate3.rl_lib import all_dists, slack_array, union_triangle_free, xor_bits


Edge = tuple[int, int]


def greedy_proper_edge_coloring(edges: tuple[Edge, ...] | list[Edge]) -> tuple[int, ...]:
    """Return a deterministic proper coloring (not claimed optimal)."""

    edges = tuple(tuple(sorted(edge)) for edge in edges)
    colors: list[int] = []
    for index, (u, v) in enumerate(edges):
        forbidden = {
            colors[j]
            for j, (a, b) in enumerate(edges[:index])
            if u in (a, b) or v in (a, b)
        }
        color = 0
        while color in forbidden:
            color += 1
        colors.append(color)
    return tuple(colors)


def minimum_proper_edge_coloring(
    edges: tuple[Edge, ...] | list[Edge],
) -> tuple[int, ...]:
    """Find a minimum proper edge coloring by exact backtracking.

    This is only for small hostile fixtures and discovery.  The mathematical
    construction merely assumes any proper coloring certificate.
    """

    edges = tuple(tuple(sorted(edge)) for edge in edges)
    if not edges:
        return ()
    conflict = [set() for _ in edges]
    for i, (u, v) in enumerate(edges):
        for j, (a, b) in enumerate(edges[:i]):
            if u in (a, b) or v in (a, b):
                conflict[i].add(j)
                conflict[j].add(i)
    order = sorted(range(len(edges)), key=lambda i: (-len(conflict[i]), edges[i]))
    degree = {}
    for u, v in edges:
        degree[u] = degree.get(u, 0) + 1
        degree[v] = degree.get(v, 0) + 1
    lower = max(degree.values())

    def color_with(k: int) -> tuple[int, ...] | None:
        assigned = [-1] * len(edges)

        def search(position: int) -> bool:
            if position == len(order):
                return True
            edge_index = order[position]
            forbidden = {
                assigned[j] for j in conflict[edge_index] if assigned[j] >= 0
            }
            for color in range(k):
                if color in forbidden:
                    continue
                assigned[edge_index] = color
                if search(position + 1):
                    return True
                assigned[edge_index] = -1
            return False

        return tuple(assigned) if search(0) else None

    for color_count in range(lower, len(edges) + 1):
        result = color_with(color_count)
        if result is not None:
            return result
    raise AssertionError("every finite edge set has the unique-edge coloring")


def _bipartite_components(n: int, edges: list[Edge]) -> tuple[list[int], list[set[int]]]:
    adjacency = adj_masks(n, edges)
    sides = [-1] * n
    components: list[set[int]] = []
    for start in range(n):
        if sides[start] >= 0:
            continue
        sides[start] = 0
        component = {start}
        stack = [start]
        while stack:
            u = stack.pop()
            neighbors = adjacency[u]
            while neighbors:
                v = (neighbors & -neighbors).bit_length() - 1
                neighbors &= neighbors - 1
                if sides[v] < 0:
                    sides[v] = 1 - sides[u]
                    component.add(v)
                    stack.append(v)
                else:
                    assert sides[v] != sides[u]
        components.append(component)
    return sides, components


@dataclass(frozen=True)
class DistanceFourCompletion:
    order: int
    endpoint_count: int
    color_count: int
    b_edges: tuple[Edge, ...]
    m_edges: tuple[Edge, ...]
    bridge_edges: tuple[Edge, ...]
    colors: tuple[int, ...]
    completion_distances: tuple[int, ...]
    minimum_cut_slack: int


def build_distance_four_completion(
    *,
    m_edges: tuple[Edge, ...] | list[Edge],
    colors: tuple[int, ...] | list[int] | None = None,
    check_all_cuts: bool = True,
) -> DistanceFourCompletion:
    """Build the exact order ``2r+k`` distance-four completion."""

    # Preserve caller order because a supplied color tuple is indexed by it.
    m_edges = tuple(tuple(sorted(edge)) for edge in m_edges)
    assert m_edges and len(set(m_edges)) == len(m_edges)
    endpoints = sorted({vertex for edge in m_edges for vertex in edge})
    endpoint_index = {vertex: index for index, vertex in enumerate(endpoints)}
    compact_m = tuple(
        tuple(sorted((endpoint_index[u], endpoint_index[v]))) for u, v in m_edges
    )
    r = len(endpoints)
    if colors is None:
        colors = minimum_proper_edge_coloring(compact_m)
    colors = tuple(colors)
    assert len(colors) == len(compact_m) and all(color >= 0 for color in colors)
    for i, (u, v) in enumerate(compact_m):
        for j, (a, b) in enumerate(compact_m[:i]):
            if u in (a, b) or v in (a, b):
                assert colors[i] != colors[j]
    used_colors = sorted(set(colors))
    color_index = {color: index for index, color in enumerate(used_colors)}
    normalized_colors = tuple(color_index[color] for color in colors)
    k = len(used_colors)

    def port(vertex: int) -> int:
        return r + vertex

    def center(color: int) -> int:
        return 2 * r + color

    b_edges: list[Edge] = []
    for (u, v), color in zip(compact_m, normalized_colors):
        b_edges.extend(
            [
                tuple(sorted((u, port(v)))),
                tuple(sorted((port(v), center(color)))),
                tuple(sorted((center(color), port(u)))),
                tuple(sorted((port(u), v))),
            ]
        )
    assert len(set(b_edges)) == 4 * len(compact_m)
    order = 2 * r + k

    # Reused colors can already connect different demand components.  Join
    # whatever supply components remain by bridges.  A bridge between old
    # components cannot create a two-edge route for an existing demand.
    _, components = _bipartite_components(order, b_edges)
    bridge_edges: list[Edge] = []
    for left, right in zip(components, components[1:]):
        # Every component contains both endpoint-side and port-side vertices.
        left_endpoint = min(vertex for vertex in left if vertex < r)
        right_port = min(vertex for vertex in right if r <= vertex < 2 * r)
        bridge = tuple(sorted((left_endpoint, right_port)))
        assert bridge not in b_edges
        b_edges.append(bridge)
        bridge_edges.append(bridge)

    _bipartite_components(order, b_edges)
    assert union_triangle_free(order, b_edges, compact_m)
    distances = all_dists(order, b_edges)
    completion_distances = tuple(distances[u][v] for u, v in compact_m)
    assert completion_distances == (4,) * len(compact_m)

    minimum_cut_slack = 0
    if check_all_cuts:
        bit = xor_bits(order)
        slack = slack_array(order, b_edges, compact_m, bit)
        minimum_cut_slack = int(slack.min())
        assert minimum_cut_slack >= 0
    return DistanceFourCompletion(
        order=order,
        endpoint_count=r,
        color_count=k,
        b_edges=tuple(b_edges),
        m_edges=compact_m,
        bridge_edges=tuple(bridge_edges),
        colors=normalized_colors,
        completion_distances=completion_distances,
        minimum_cut_slack=minimum_cut_slack,
    )
