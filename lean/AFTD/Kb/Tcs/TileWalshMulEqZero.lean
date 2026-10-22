import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tile_walsh_mul_eq_zero

Topic: combinatorics   Node: 4c3aebf538a5

Provenance: formalization of a published result. Source: arXiv:2610.24022, equation (2.2)

Let E and T be subsets of Fin d → ZMod 2 such that E + T is the universal set and |E| * |T| = 2^d. For every nonzero vector u : Fin d → ZMod 2, the product of the character sums (∑ e ∈ E, (-1 : ℤ) ^ (dotProduct u e).val) and (∑ t ∈ T, (-1 : ℤ) ^ (dotProduct u t).val) is equal to 0.
-/

open scoped Pointwise Matrix

lemma tile_walsh_mul_eq_zero_zmod2_neg_one_pow_add (a b : ZMod 2) :
    (-1 : ℤ) ^ (a + b).val = (-1 : ℤ) ^ a.val * (-1 : ℤ) ^ b.val := by
  revert a b
  decide

lemma tile_walsh_mul_eq_zero_zmod2_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  revert a ha
  decide

lemma tile_walsh_mul_eq_zero_sum_univ {d : ℕ} (u : Fin d → ZMod 2) (hu : u ≠ 0) :
    ∑ x : Fin d → ZMod 2, (-1 : ℤ) ^ (dotProduct u x).val = 0 := by
  have ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra! h
    apply hu
    ext j
    exact h j
  have huj : u j = 1 := tile_walsh_mul_eq_zero_zmod2_eq_one_of_ne_zero (u j) hj
  let c : Fin d → ZMod 2 := Pi.single j 1
  let e := Equiv.addRight c
  have hsum : ∑ x, (-1 : ℤ) ^ (dotProduct u x).val =
      ∑ x, (-1 : ℤ) ^ (dotProduct u (e x)).val := (Equiv.sum_comp e _).symm
  have hterm (x : Fin d → ZMod 2) :
      (-1 : ℤ) ^ (dotProduct u (e x)).val = - (-1 : ℤ) ^ (dotProduct u x).val := by
    dsimp [e, c]
    rw [dotProduct_add, dotProduct_single, huj, mul_one]
    rw [tile_walsh_mul_eq_zero_zmod2_neg_one_pow_add]
    have : (1 : ZMod 2).val = 1 := rfl
    rw [this]
    ring
  rw [Fintype.sum_congr _ _ hterm] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  linarith

lemma tile_walsh_mul_eq_zero_image_add_eq {d : ℕ} (E T : Finset (Fin d → ZMod 2)) :
    (E ×ˢ T).image (fun p => p.1 + p.2) = E + T := by
  ext x
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_add, Prod.exists]
  tauto

open scoped Pointwise Matrix in
/-- Convolution orthogonality of character sums for translational tiling pairs in (ZMod 2)^d. -/
theorem tile_walsh_mul_eq_zero {d : ℕ} (E T : Finset (Fin d → ZMod 2))
    (hET : E + T = Finset.univ) (hcard : E.card * T.card = 2 ^ d)
    (u : Fin d → ZMod 2) (hu : u ≠ 0) :
    (∑ e ∈ E, (-1 : ℤ) ^ (dotProduct u e).val) * (∑ t ∈ T, (-1 : ℤ) ^ (dotProduct u t).val) = 0 := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hsum : ∑ p ∈ E ×ˢ T, (-1 : ℤ) ^ (dotProduct u p.1).val * (-1 : ℤ) ^ (dotProduct u p.2).val =
      ∑ p ∈ E ×ˢ T, (-1 : ℤ) ^ (dotProduct u (p.1 + p.2)).val := by
    apply Finset.sum_congr rfl
    intro p _
    rw [dotProduct_add, tile_walsh_mul_eq_zero_zmod2_neg_one_pow_add]
  rw [hsum]
  let f : (Fin d → ZMod 2) × (Fin d → ZMod 2) → (Fin d → ZMod 2) := fun p => p.1 + p.2
  have himage : (E ×ˢ T).image f = Finset.univ := by
    rw [tile_walsh_mul_eq_zero_image_add_eq, hET]
  have hcard_univ : (Finset.univ : Finset (Fin d → ZMod 2)).card = 2 ^ d := by simp
  have hinj : Set.InjOn f ↑(E ×ˢ T) := by
    rw [← Finset.card_image_iff, himage, hcard_univ, Finset.card_product, hcard]
  have hsum_univ := @Finset.sum_image _ _ ℤ _ (fun x => (-1 : ℤ) ^ (dotProduct u x).val) _ (E ×ˢ T) f hinj
  rw [himage] at hsum_univ
  rw [← hsum_univ]
  exact tile_walsh_mul_eq_zero_sum_univ u hu
