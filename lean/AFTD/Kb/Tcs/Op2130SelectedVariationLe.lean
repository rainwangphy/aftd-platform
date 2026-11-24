import AFTD.Prelude

/-!
# op2130_selected_variation_le

Topic: online_algorithms   Node: d3ab51e1b161

Provenance: helper lemma. OP-2130, projection of quadratic variation

The sum of squared increments along an injectively selected set of coin positions is at most the sum across the full tape.
-/

theorem op2130_selected_variation_le (T m : ℕ) (idx : Fin m → Fin T)
    (hinj : Function.Injective idx) (a : ℕ → ℝ) :
    (∑ j : Fin m, (a (idx j).val)^2) ≤ ∑ t ∈ Finset.range T, (a t)^2 := by
  classical
  let s := Finset.univ.image fun j : Fin m => (idx j).val
  have hs : s ⊆ Finset.range T := by
    intro t ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_range.mpr (idx j).isLt
  have hsum : (∑ t ∈ s, (a t)^2) = ∑ j : Fin m, (a (idx j).val)^2 := by
    dsimp only [s]
    apply Finset.sum_image
    intro i hi j hj h
    apply hinj
    exact Fin.ext h
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (by intro i hi his; positivity)
