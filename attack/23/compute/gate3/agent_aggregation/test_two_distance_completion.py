from compute23.gate3.agent_aggregation.two_distance_completion import (
    build_distinct_two_distance_completion,
    build_equal_two_distance_completion,
)


def test_dangerous_four_eight_profile_has_order_eleven() -> None:
    completion = build_distinct_two_distance_completion(4, 8)
    assert completion.order == 11
    assert completion.completion_distances == (4, 8)
    assert completion.minimum_cut_slack == 0


def test_mixed_four_six_profile_improves_to_order_nine() -> None:
    completion = build_distinct_two_distance_completion(4, 6)
    assert completion.order == 9
    assert completion.completion_distances == (4, 6)
    assert completion.minimum_cut_slack == 0


def test_six_eight_profile_has_order_twelve() -> None:
    completion = build_distinct_two_distance_completion(6, 8)
    assert completion.order == 12
    assert completion.completion_distances == (6, 8)
    assert completion.minimum_cut_slack == 0


def test_equal_distance_four_uses_two_lanes_in_order_eight() -> None:
    completion = build_equal_two_distance_completion(4)
    assert completion.order == 8
    assert completion.completion_distances == (4, 4)
    assert completion.minimum_cut_slack == 0


def test_equal_distance_eight_general_layering() -> None:
    completion = build_equal_two_distance_completion(8)
    assert completion.order == 14
    assert completion.completion_distances == (8, 8)
    assert completion.minimum_cut_slack == 0
