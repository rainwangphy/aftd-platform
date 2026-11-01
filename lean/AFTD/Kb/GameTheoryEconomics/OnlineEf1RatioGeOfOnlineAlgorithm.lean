import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineEf1ApproximationRatio
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm

/-!
# online_ef1_ratio_ge_of_online_algorithm

Topic: fair_division   Node: c3cf95ab090e

Provenance: helper lemma. step towards op561_ratio_gt_sqrt5

If alpha lies in [0,1] and some deterministic online algorithm guarantees an alpha-EF1 allocation for n agents under exact frequency predictions, then alpha is at most the online EF1 approximation ratio (the supremum of all such ratios).
-/

theorem online_ef1_ratio_ge_of_online_algorithm (n : ℕ) {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (h : has_online_alpha_ef1_algorithm n α) : α ≤ online_ef1_approximation_ratio n := by
  unfold online_ef1_approximation_ratio
  have hbdd : BddAbove {β : ℝ | 0 ≤ β ∧ β ≤ 1 ∧ has_online_alpha_ef1_algorithm n β} := by
    use 1
    intro x hx
    exact hx.2.1
  have hmem : α ∈ {β : ℝ | 0 ≤ β ∧ β ≤ 1 ∧ has_online_alpha_ef1_algorithm n β} := ⟨h0, h1, h⟩
  exact le_csSup hbdd hmem
