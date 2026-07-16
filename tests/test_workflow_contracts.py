"""Contracts that keep expensive external audits outside routine automation."""

from pathlib import Path
import re

import yaml


ROOT = Path(__file__).parents[1]


def test_heavy_lean_reaudit_is_manual_only():
    workflow = yaml.load(
        (ROOT / ".github" / "workflows" / "audit-proofs.yml").read_text(),
        Loader=yaml.BaseLoader,
    )

    assert workflow["on"] == {"workflow_dispatch": {}}


def test_frontier_workflow_uses_the_lock_matching_released_vela():
    workflow = yaml.load(
        (ROOT / ".github" / "workflows" / "vela-frontier.yml").read_text(),
        Loader=yaml.BaseLoader,
    )
    lock = (ROOT / "vela.lock").read_text()
    lock_version = re.search(r"^vela_version:\s*(\S+)$", lock, re.MULTILINE)

    assert lock_version is not None
    assert workflow["env"]["VELA_VERSION"] == f"v{lock_version.group(1)}"
    assert workflow["env"]["VELA_RELEASE_COMMIT"] == (
        "4c963ba66026d5e699419d074db3c18a5bc12233"
    )
    assert workflow["env"]["VELA_LINUX_SHA256"] == (
        "766402ab20c82645740ff579d8360a5454395cd0d07c2c96486169a952a354cc"
    )
