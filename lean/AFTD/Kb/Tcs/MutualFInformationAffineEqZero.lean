import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_affine_eq_zero

Topic: information   Node: 2c02c3e97e7a

Provenance: helper lemma. Helper for mutual_f_information_subadditive_add_affine_iff (OP-331): the generator c(t - 1) gives zero mutual f-information.

For a joint probability mass function p on finite sets (p ≥ 0, total mass 1) and any real c, the mutual f-information with generator t ↦ c (t - 1) is 0.
-/

theorem mutual_f_information_affine_eq_zero {X Y : Type*} [Fintype X] [Fintype Y] (c : ℝ)
    (p : X → Y → ℝ) (hp : ∀ x y, 0 ≤ p x y) (hs : ∑ x, ∑ y, p x y = 1) :
    mutual_f_information (fun t => c * (t - 1)) p = 0 := by
  have hkey : ∀ x y, (∑ y', p x y') * (∑ x', p x' y) *
      (c * (p x y / ((∑ y', p x y') * (∑ x', p x' y)) - 1)) =
      c * (p x y - (∑ y', p x y') * (∑ x', p x' y)) := by
    intro x y
    by_cases h0 : (∑ y', p x y') * (∑ x', p x' y) = 0
    · have hle1 : p x y ≤ ∑ y', p x y' :=
        Finset.single_le_sum (f := fun y' => p x y') (fun y' _ => hp x y') (Finset.mem_univ y)
      have hle2 : p x y ≤ ∑ x', p x' y :=
        Finset.single_le_sum (f := fun x' => p x' y) (fun x' _ => hp x' y) (Finset.mem_univ x)
      have hpxy : p x y = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact le_antisymm (h ▸ hle1) (hp x y)
        · exact le_antisymm (h ▸ hle2) (hp x y)
      rw [h0, hpxy]; simp
    · generalize (∑ y', p x y') * (∑ x', p x' y) = DD at h0 ⊢
      have hD : DD * (p x y / DD) = p x y := by field_simp
      rw [show DD * (c * (p x y / DD - 1)) = c * (DD * (p x y / DD) - DD) by ring, hD]
  have h3 : ∑ i, ∑ x', p x' i = 1 := by rw [Finset.sum_comm]; exact hs
  simp only [mutual_f_information, hkey, ← Finset.mul_sum, Finset.sum_sub_distrib, h3,
    mul_one, sub_self, mul_zero, Finset.sum_const_zero]
