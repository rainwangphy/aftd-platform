import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PluralityRegularizationThreshold

/-!
# plurality_regularization_threshold_pos

Topic: social_choice   Node: 5c8c29b3b351

Provenance: helper lemma. folklore

For any number of candidates m ≥ 3 and number of voters n ≥ max(8, m), the plurality regularization threshold plurality_regularization_threshold n m = 1 / ((m - 2)n - 2m) is strictly positive.
-/

/-- The plurality regularization threshold is strictly positive for m ≥ 3 and n ≥ max(8, m). -/
theorem plurality_regularization_threshold_pos (m n : ℕ) (hm : 3 ≤ m) (hn : max 8 m ≤ n) : 0 < plurality_regularization_threshold n m := by
  unfold plurality_regularization_threshold
  rw [one_div_pos]
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hn8 : 8 ≤ n := le_of_max_le_left hn
  have hnR : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  nlinarith
