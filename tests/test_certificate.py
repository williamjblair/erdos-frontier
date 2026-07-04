"""The machine-facts certificate generator emits the verdict fields honestly."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from certificate import certificate


def test_unconditional_row():
    cert = certificate({
        "problem": 16, "erdos_url": "https://www.erdosproblems.com/16",
        "fc_theorem": "Erdos16.erdos_16", "machine_source": "plby",
        "machine_verdict": "unconditional", "non_kernel_axioms": [],
        "named_assumptions": [], "proof_link": "https://example.com/Erdos16.lean",
    })
    assert cert["verdict"] == "unconditional"
    assert cert["checks"]["axioms_beyond_standard"] == []
    assert cert["checks"]["hypothesis_parameters"] == []
    assert cert["layer"] == "evidence"


def test_conditional_by_axiom():
    cert = certificate({
        "problem": 997, "erdos_url": "https://www.erdosproblems.com/997",
        "fc_theorem": "Erdos997.erdos_997", "machine_source": "plby",
        "machine_verdict": "conditional", "non_kernel_axioms": ["maynardTaoBFT"],
        "named_assumptions": [], "proof_link": "https://example.com/Erdos997.lean",
    })
    assert cert["verdict"] == "conditional"
    assert "maynardTaoBFT" in cert["verdict_basis"]
    assert cert["checks"]["axioms_beyond_standard"] == ["maynardTaoBFT"]


def test_conditional_by_hypothesis_parameter():
    """The case an axiom check misses: a Prop hypothesis taken as a parameter."""
    cert = certificate({
        "problem": 1148, "erdos_url": "https://www.erdosproblems.com/1148",
        "fc_theorem": "Erdos1148.erdos_1148", "machine_source": "plby",
        "machine_verdict": "conditional", "non_kernel_axioms": [],
        "named_assumptions": ["h_duke : Erdos1148.DukeTheoremStatement"],
        "proof_link": None,
    })
    assert cert["verdict"] == "conditional"
    assert "parameters" in cert["verdict_basis"]
    assert cert["checks"]["hypothesis_parameters"] == ["h_duke : Erdos1148.DukeTheoremStatement"]
