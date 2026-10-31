import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1AlgorithmZero
import AFTD.Kb.GameTheoryEconomics.OnlineEf1ApproximationRatio
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm

/-!
# op561_exists_of_ratio_gt

Topic: fair_division   Node: c3e40ef49dfa

Provenance: helper lemma. step towards op561_exists_online_algorithm_gt_sqrt5

If the online EF1 approximation ratio for four agents strictly exceeds (3 - sqrt 5)/2, then there exists an achievable approximation ratio alpha strictly exceeding (3 - sqrt 5)/2.
-/

/-- If the online EF1 approximation ratio for four agents strictly exceeds (3 - sqrt 5)/2, then there exists an achievable approximation ratio alpha strictly exceeding (3 - sqrt 5)/2. -/
theorem op561_exists_of_ratio_gt (h : (3 - Real.sqrt 5) / 2 < online_ef1_approximation_ratio 4) :
    ∃ α : ℝ, (3 - Real.sqrt 5) / 2 < α ∧ has_online_alpha_ef1_algorithm 4 α := by
  have h_ne : {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧ has_online_alpha_ef1_algorithm 4 α}.Nonempty :=
    ⟨0, le_rfl, by norm_num, has_online_alpha_ef1_algorithm_zero 4⟩
  obtain ⟨α, hα, hlt⟩ := exists_lt_of_lt_csSup h_ne h
  exact ⟨α, hlt, hα.2.2⟩
