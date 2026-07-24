"""Contracts that keep expensive external audits outside routine automation."""

from pathlib import Path
import json
import re
import subprocess

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
    checkout = workflow["jobs"]["verify"]["steps"][0]
    assert checkout["with"]["fetch-depth"] == "0"
    assert workflow["env"]["VELA_LINUX_ARCHIVE_SHA256"] == (
        "b0886a25ea22eb0bd1be957e3a997a527ff21b265dc4dbdb3a948f9432dc2d52"
    )
    assert workflow["env"]["VELA_LINUX_SHA256"] == (
        "d8bf9c6e708cff8837601b4cd675085dcaedc08d37368eeb4077d0219462d754"
    )
    boundary_root = "sha256:4391ce03513626317287c92681c04da7f6b9813d70d01cd300d46b38adfd6fae"
    assert workflow["env"]["VELA_REPOSITORY_BOUNDARY_ROOT"] == boundary_root
    trust_step = next(
        step
        for step in workflow["jobs"]["verify"]["steps"]
        if step.get("name") == "Install the reviewed consumer trust anchor"
    )
    anchor = json.loads(
        (ROOT / ".github" / "consumer-trust" / "vfr_0a25edabc16db143.json").read_text()
    )
    assert anchor == {
        "schema": "vela.repository-trust-anchor.v1",
        "frontier_id": "vfr_0a25edabc16db143",
        "identity_root": "sha256:a767c4b5c4645ebcbb3862c20a8cbd533bcd7f05f112f2423f4c6c76573e9b45",
        "boundary_content_root": boundary_root,
        "administrator_actor_id": "reviewer:will-blair",
        "administrator_public_key": "4892f93877e637b5f59af31d9ec6704814842fb278cacb0eb94704baef99455e",
    }
    assert "install -m 0600" in trust_step["run"]


def test_artifact_hash_cannot_depend_on_ignored_workspace_files():
    ignored = subprocess.run(
        [
            "git",
            "ls-files",
            "--others",
            "--ignored",
            "--exclude-standard",
            "artifacts",
        ],
        cwd=ROOT,
        check=True,
        text=True,
        capture_output=True,
    ).stdout.splitlines()

    assert ignored == []
