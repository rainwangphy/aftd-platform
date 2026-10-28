import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineEf1ApproximationRatio
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm

/-!
# online_ef1_approximation_ratio_le_one

Topic: fair_division   Node: 476d995bb1a1

Provenance: helper lemma. step towards op561_tight_ef1_factor_four_agents

For any number of agents n, the online EF1 approximation ratio is at most 1.
-/

/-- The online EF1 approximation ratio for any number of agents is at most 1, by definition as the supremum of a subset of [0, 1]. -/
theorem online_ef1_approximation_ratio_le_one (n : ℕ) :
    online_ef1_approximation_ratio n ≤ 1 := by
  unfold online_ef1_approximation_ratio
  apply Real.sSup_le
  · intro x hx
    exact hx.2.1
  · norm_num
