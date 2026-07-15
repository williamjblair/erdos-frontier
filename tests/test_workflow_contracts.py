"""Contracts that keep expensive external audits outside routine automation."""

from pathlib import Path

import yaml


ROOT = Path(__file__).parents[1]


def test_heavy_lean_reaudit_is_manual_only():
    workflow = yaml.load(
        (ROOT / ".github" / "workflows" / "audit-proofs.yml").read_text(),
        Loader=yaml.BaseLoader,
    )

    assert workflow["on"] == {"workflow_dispatch": {}}
