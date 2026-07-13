from collections import Counter
from pathlib import Path

import yaml


ROOT = Path(__file__).resolve().parents[1]


def test_formal_conjectures_activity_matches_registry_partition():
    registry = yaml.safe_load((ROOT / "sources/work-registry.yaml").read_text())
    manifest = yaml.safe_load(
        (ROOT / "sources/formal-conjectures-activity.yaml").read_text()
    )

    repo = registry["repositories"]["formal_conjectures"]
    authored = registry["inventory"]["formal_conjectures_authored"]
    partition = registry["inventory"]["formal_conjectures_classification"]
    expected = {
        problem: category
        for category, problems in partition.items()
        for problem in problems
    }
    rows = manifest["problems"]

    assert manifest["schema"] == "erdos-frontier.formal-conjectures-activity.v1"
    assert manifest["source"]["repository"] == repo["remote"]
    assert manifest["source"]["pinned_commit"] == repo["commit"]
    assert len(expected) == len(authored) == len(rows) == 136
    assert [row["problem"] for row in rows] == sorted(authored)
    assert len({row["problem"] for row in rows}) == 136
    assert {row["problem"]: row["category"] for row in rows} == expected

    counts = Counter(row["category"] for row in rows)
    assert dict(sorted(counts.items())) == manifest["summary"]["category_counts"]
    assert manifest["summary"]["authored_problem_count"] == 136
    assert all(
        row["affects_mathematical_work_lens"]
        == (row["category"] == "mathematical_proof_work")
        for row in rows
    )
    assert manifest["policy"]["mathematical_lens_category"] == "mathematical_proof_work"
    assert manifest["policy"]["note"].startswith("Only mathematical_proof_work")
