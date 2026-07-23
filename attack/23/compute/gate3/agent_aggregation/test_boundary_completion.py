from compute23.gate2.common import parse_graph6

from compute23.gate3.agent_aggregation.boundary_completion import (
    build_boundary_completion,
)


def test_boundary_completion_preserves_validity_and_distances() -> None:
    # Start with the exact n=9 rooted fixture whose seven-vertex off-path
    # component contains two distance-four M-edges and has two attachments at
    # path coordinate zero.  Append a five-edge rooted tail at vertex zero so
    # the valid completion is strictly smaller than the ambient instance.
    base_n, base_b = parse_graph6("H??CFbK")
    assert base_n == 9
    base_m = ((2, 4), (3, 5))
    tail = tuple(range(base_n, base_n + 5))
    b_edges = list(base_b) + [(0, tail[0])] + list(zip(tail, tail[1:]))
    path = (0,) + tail
    component = (1, 2, 3, 4, 5, 7, 8)
    completion = build_boundary_completion(
        n=base_n + len(tail),
        b_edges=b_edges,
        m_edges=base_m,
        path=path,
        component=component,
    )
    assert completion.spoke_lengths == (2, 2)
    assert completion.order == 10 < base_n + len(tail)
    assert completion.ambient_m_distances == (4, 4)
    assert completion.component_m_distances == (4, 4)
    assert completion.completion_m_distances == (4, 4)
    assert completion.minimum_cut_slack == 0


def test_mixed_attachment_parities_use_two_spoke_lengths() -> None:
    n, b_edges = parse_graph6("G?BfEo")
    completion = build_boundary_completion(
        n=n,
        b_edges=b_edges,
        m_edges=((2, 3), (2, 4)),
        path=(0, 5),
        component=(1, 2, 3, 4, 6, 7),
    )
    assert sorted(completion.spoke_lengths) == [2, 2, 3, 3]
    assert completion.order == 13
    assert completion.ambient_m_distances == (4, 4)
    assert completion.completion_m_distances == (4, 4)
    assert completion.minimum_cut_slack == 0
