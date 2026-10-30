import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineEf1ApproximationRatio
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm

/-!
# online_ef1_approximation_ratio_nonneg

Topic: fair_division   Node: 4ed889ce78b4

Provenance: helper lemma. arXiv:2610.34625

For any number of agents n, the online EF1 approximation ratio under exact frequency predictions is nonnegative.
-/

/-- The online EF1 approximation ratio under exact frequency predictions is always nonnegative. -/
theorem online_ef1_approximation_ratio_nonneg (n : ℕ) :
    0 ≤ online_ef1_approximation_ratio n := by
  unfold online_ef1_approximation_ratio
  apply Real.sSup_nonneg
  intro x hx
  exact hx.1
