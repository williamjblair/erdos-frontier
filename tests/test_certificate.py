"""The certificate is a faithful projection of the two frontier tiers."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from certificate import evidence_layer, faithfulness_layer, certificate


def test_evidence_conditional_by_hypothesis_parameter():
    """The case an axiom check misses: kernel-clean but a Prop hypothesis param."""
    ev = evidence_layer({
        "fc_theorem": "Erdos224.erdos_224", "machine_source": "plby",
        "machine_verdict": "conditional", "non_kernel_axioms": [],
        "named_assumptions": ["hNo : Erdos224.NoObtuse A"],
        "proof_link": "https://example.com/Erdos224.lean",
    })
    assert ev["verdict"] == "conditional"
    assert ev["hypothesis_parameters"] == ["hNo : Erdos224.NoObtuse A"]
    assert "axiom check does not see" in ev["verdict_basis"]


def test_evidence_unconditional():
    ev = evidence_layer({
        "fc_theorem": "Erdos16.erdos_16", "machine_source": "plby",
        "machine_verdict": "unconditional", "non_kernel_axioms": [],
        "named_assumptions": [], "proof_link": "https://example.com/x.lean",
    })
    assert ev["verdict"] == "unconditional"


def test_faithfulness_serializes_the_real_signature():
    att = {
        "verdict": "faithful", "attested_by": "reviewer:will-blair",
        "id": "vsa_923f442721de9905", "target": "vf_f4943511fd2af2d2",
        "formal_ref": "FormalConjectures/ErdosProblems/224.lean@5beb6f5da3a9",
        "formal_statement_hash": "e0f4ceef", "note": "batch-2a",
        "signer_pubkey_hex": "4892f938", "signature": "d71dffb9",
        "attested_at": "2026-07-02T14:43:10Z",
    }
    f = faithfulness_layer(att)
    assert f["present"] and f["verdict"] == "faithful"
    assert f["attestation_id"] == "vsa_923f442721de9905"
    assert f["signature"] == "d71dffb9"  # the real Ed25519 sig is carried through
    assert f["formal_statement_hash"] == "sha256:e0f4ceef"


def test_faithfulness_absent_is_honest():
    f = faithfulness_layer(None)
    assert f["present"] is False
    assert "verdict" not in f


def test_two_layers_are_independent():
    """A proof can be unconditional yet the statement unfaithful (#214)."""
    cert = certificate(
        {"problem": 214, "erdos_url": "https://www.erdosproblems.com/214",
         "fc_theorem": "Erdos214.theorem_1", "machine_source": "plby",
         "machine_verdict": "unconditional", "non_kernel_axioms": [],
         "named_assumptions": [], "proof_link": None},
        {"verdict": "unfaithful", "attested_by": "reviewer:will-blair",
         "id": "vsa_cce05f44f38a76ed", "target": "vf_x", "formal_ref": "x@y",
         "formal_statement_hash": "ab", "note": "", "signer_pubkey_hex": "cd",
         "signature": "ef", "attested_at": "2026-07-02T14:43:10Z"},
        "vfr_0a25edabc16db143")
    assert cert["evidence"]["verdict"] == "unconditional"
    assert cert["faithfulness"]["verdict"] == "unfaithful"
