import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimPredictedGrundy
import AFTD.Kb.GameTheoryEconomics.SlowExactNimTruncationBound
import AFTD.Kb.GameTheoryEconomics.SlowExactNimTruncate

/-!
# slow_exact_nim_predicted_grundy_zero

Topic: combinatorial_games   Node: 3e03711d0254

Provenance: helper lemma. arXiv:2611.14546:470

For every integer k ≥ 2, the explicit formula slow_exact_nim_predicted_grundy k evaluated on the zero position equals 0.
-/

/-- Sanity check: the explicit formula gives 0 on the zero position. -/
theorem slow_exact_nim_predicted_grundy_zero (k : ℕ) (hk : 2 ≤ k) :
    slow_exact_nim_predicted_grundy k (fun _ => 0) = 0 := by
  unfold slow_exact_nim_predicted_grundy slow_exact_nim_truncate
  simp
  omega
