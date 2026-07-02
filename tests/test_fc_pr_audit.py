"""Parser tests for fc_pr_audit's textual Lean reading."""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))

from fc_pr_audit import parse_lean

SAMPLE = '''\
import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 999

*References:*
- [erdosproblems.com/999](https://www.erdosproblems.com/999)
-/

namespace Erdos999

/-- A helper set. -/
def A : Set ℕ := sorry

/--
Is every widget a gadget?
-/
@[category research open, AMS 5 11]
theorem erdos_999 : answer(sorry) ↔ True := by
  sorry

@[category research solved, AMS 11,
  formal_proof using lean4 at "https://example.com/proof.lean"]
theorem erdos_999.variants.solved : True := by
  trivial

@[category textbook, AMS 5]
theorem erdos_999.variants.textbook : True := by
  trivial

end Erdos999
'''


def test_declarations_and_attributes():
    parsed = parse_lean(SAMPLE)
    by_name = {d["name"]: d for d in parsed["decls"]}
    assert set(by_name) == {"A", "erdos_999", "erdos_999.variants.solved",
                            "erdos_999.variants.textbook"}
    assert by_name["A"]["kind"] == "def"
    assert by_name["A"]["category"] is None
    assert by_name["A"]["docstring"] is True
    assert by_name["erdos_999"]["category"] == "research open"
    assert by_name["erdos_999"]["ams"] == "5 11"
    assert by_name["erdos_999"]["docstring"] is True
    assert by_name["erdos_999.variants.textbook"]["category"] == "textbook"


def test_multiline_attribute_and_formal_proof_link():
    parsed = parse_lean(SAMPLE)
    solved = next(d for d in parsed["decls"] if d["name"].endswith("solved"))
    assert solved["category"] == "research solved"
    assert solved["formal_proof"] == ["https://example.com/proof.lean"]


def test_erdos_reference_extraction():
    parsed = parse_lean(SAMPLE)
    assert parsed["erdos_refs"] == ["999"]
