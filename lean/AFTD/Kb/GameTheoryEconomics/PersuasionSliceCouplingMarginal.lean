import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoupling
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCardNe

/-!
# persuasion_slice_coupling_marginal

Topic: mechanism_design   Node: 977b3e5fd72a

The first marginal of the slice coupling is the slice prior.
-/

open Finset in
/-- The first marginal of the slice coupling is the slice prior. -/
lemma persuasion_slice_coupling_marginal (m : ℕ) (hm : 1 ≤ m) (x : persuasion_slice_coord m → Bool) :
    ∑ y, persuasion_slice_coupling m x y = persuasion_slice_prior m x := by
  classical
  unfold persuasion_slice_coupling persuasion_slice_prior
  rw [sum_comm]
  apply sum_congr rfl; intro s _
  rw [sum_comm]
  by_cases hs : persuasion_slice_state m s = x
  · rw [if_pos hs]
    have e : ∀ t, (∑ y, if s ≠ t ∧ persuasion_slice_state m s = x ∧
        persuasion_slice_state m t = y then 1 / ((2 * m + 1 : ℝ) * (2 * m)) else 0) =
        if s ≠ t then 1 / ((2 * m + 1 : ℝ) * (2 * m)) else 0 := by
      intro t
      by_cases ht : s ≠ t
      · simp only [ht, hs, true_and, if_true, ne_eq, not_false_eq_true]
        rw [sum_ite_eq]
        simp
      · simp [ht]
    rw [sum_congr rfl (fun t _ => e t), ← sum_filter, Finset.sum_const, persuasion_slice_card_ne,
      nsmul_eq_mul]
    have : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    push_cast
    field_simp
  · rw [if_neg hs]
    apply sum_eq_zero; intro t _
    apply sum_eq_zero; intro y _
    simp [hs]
