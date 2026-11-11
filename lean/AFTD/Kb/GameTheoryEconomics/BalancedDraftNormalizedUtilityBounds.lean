import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftNormalizedUtility
import AFTD.Kb.GameTheoryEconomics.BalancedDraftValueOrder
import AFTD.Kb.GameTheoryEconomics.DraftRule

/-!
# balanced_draft_normalized_utility_bounds

Topic: fair_division   Node: 3ec91535afd6

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

If an agent assigns nonnegative values to all goods, her normalized utility under any schedule lies between zero and the number of agents, including when total value is zero.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem balanced_draft_normalized_utility_bounds (n m : ℕ) (s : Fin m → Fin n) (v : Fin n → Fin m → ℝ)
    (i : Fin n) (hv : ∀ g, 0 ≤ v i g) :
    0 ≤ balanced_draft_normalized_utility n m s v i ∧ balanced_draft_normalized_utility n m s v i ≤ n := by
  classical
  let T := draft_rule s (fun j => balanced_draft_value_order (v j)) i
  have hs : (∑ g ∈ T, v i g) ≤ ∑ g : Fin m, v i g := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    intro g _ _
    exact hv g
  have ht : 0 ≤ ∑ g : Fin m, v i g := Finset.sum_nonneg fun g _ => hv g
  have hb : 0 ≤ ∑ g ∈ T, v i g := Finset.sum_nonneg fun g _ => hv g
  unfold balanced_draft_normalized_utility
  change 0 ≤ (n : ℝ) * (∑ g ∈ T, v i g) / (∑ g : Fin m, v i g) ∧
    (n : ℝ) * (∑ g ∈ T, v i g) / (∑ g : Fin m, v i g) ≤ n
  constructor
  · exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hb) ht
  · by_cases ht0 : (∑ g : Fin m, v i g) = 0
    · simp [ht0]
    · apply (div_le_iff₀ (lt_of_le_of_ne ht (Ne.symm ht0))).2
      exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)
