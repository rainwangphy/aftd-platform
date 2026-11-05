import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost

/-!
# line_min_matching_cost_nonneg

Topic: social_choice   Node: d1af5935cead

Provenance: helper lemma. sanity lemma for line_min_matching_cost (OP-1158)

OPT is nonnegative.
-/

theorem line_min_matching_cost_nonneg {n : ℕ} (a b : Fin n → ℝ) :
    0 ≤ line_min_matching_cost a b := by
  unfold line_min_matching_cost
  exact (Finset.le_inf'_iff _ _).2 fun σ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
