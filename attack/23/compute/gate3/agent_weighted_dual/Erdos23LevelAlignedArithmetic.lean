import ErdosProblems.Erdos23GapGBJoint

/-!
# Erdős 23: arithmetic for binary BFS layers

This scratch module isolates the exact arithmetic behind the level-aligned
multi-demand subregime.  It deliberately does not claim the graph-level
construction or full BF-RL.
-/

namespace Erdos23LevelAlignedArithmetic

/-- If `L` is the number of active level gaps and `H` the number of gaps
whose two endpoint levels both contain an extra vertex, then the interval
square envelope fits inside the parity-independent part of the RL budget.

The graph application supplies `L ≤ d`, `H ≤ L`, `L+H ≤ 2s`, and
`H ≤ s-1`.  The conclusion has been denominator-cleared by four.
-/
theorem binaryLayer_intervalEnvelope
    {s d L H : ℕ}
    (hL : L ≤ d) (hHL : H ≤ L) (hLH : L + H ≤ 2 * s)
    (hHs : H + 1 ≤ s) :
    4 * L ^ 2 + 8 * H ^ 2 + 9 * L + 18 * H ≤
      4 * s ^ 2 + 8 * s * d + 16 * s := by
  by_cases hdlo : d ≤ s - 1
  · have hLd : L ≤ s - 1 := hL.trans hdlo
    have hHd : H ≤ s - 1 := hHL.trans hLd
    nlinarith [sq_nonneg (s - 1 - L), sq_nonneg (L - H),
      sq_nonneg (s - 1 - H)]
  · have hsd : s ≤ d + 1 := by omega
    by_cases hdhi : s + 1 ≤ d
    · by_cases hHd : H ≤ 2 * s - d
      · have hLd' : L ≤ d := hL
        nlinarith [sq_nonneg (d - L), sq_nonneg (2 * s - d - H),
          sq_nonneg H]
      · have hHlarge : 2 * s - d ≤ H := by omega
        have hLsum : L ≤ 2 * s - H := by omega
        nlinarith [sq_nonneg (2 * s - H - L),
          sq_nonneg (H - (2 * s - d)), sq_nonneg (s - 1 - H)]
    · have hdmid : d ≤ s := by omega
      have hLs : L ≤ s := hL.trans hdmid
      have hHsm : H ≤ s - 1 := by omega
      nlinarith [sq_nonneg (s - L), sq_nonneg (s - 1 - H),
        sq_nonneg (L - H)]

/-- The exact RL budget always contains the parity-independent envelope used
by `binaryLayer_intervalEnvelope`, since `partnerDistance d ≥ 1`. -/
theorem parityIndependentBudget_le_rlBudget (s d : ℕ) :
    s ^ 2 + 2 * s * d + 4 * s ≤
      Erdos23GapGBSeries.rlBudget s d := by
  have hp := Erdos23GapGBSeries.partnerDistance_pos d
  unfold Erdos23GapGBSeries.rlBudget
  nlinarith

#print axioms binaryLayer_intervalEnvelope
#print axioms parityIndependentBudget_le_rlBudget

end Erdos23LevelAlignedArithmetic
