import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130SelectedVariationLe

/-!
# op2130_variation_projection_reduction

Topic: online_algorithms   Node: a59ae56b85b7

Provenance: helper lemma. OP-2130, selected coin variation

If the full-tape conditional means before and after each distinct selected coin agree with the corresponding reduced-tape means, then the reduced quadratic variation is bounded by the full quadratic variation.
-/

theorem op2130_variation_projection_reduction (T m : ℕ) (idx : Fin m → Fin T)
    (hinj : Function.Injective idx) (M R : ℕ → ℝ)
    (h : ∀ j : Fin m, M (idx j).val = R j.val ∧ M ((idx j).val+1) = R (j.val+1)) :
    (∑ j ∈ Finset.range m, (R (j+1) - R j)^2) ≤
      ∑ t ∈ Finset.range T, (M (t+1) - M t)^2 := by
  have hs := op2130_selected_variation_le T m idx hinj (fun t => M (t+1)-M t)
  have he : (∑ j : Fin m, (R (j.val+1)-R j.val)^2) =
      ∑ j : Fin m, (M ((idx j).val+1)-M (idx j).val)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [(h j).1,(h j).2]
  rw [← he] at hs
  have hrange : (∑ j ∈ Finset.range m, (R (j+1) - R j)^2) =
      ∑ j : Fin m, (R (j.val+1)-R j.val)^2 := by
    exact (Fin.sum_univ_eq_sum_range (fun j => (R (j+1)-R j)^2) m).symm
  rw [hrange]
  exact hs
