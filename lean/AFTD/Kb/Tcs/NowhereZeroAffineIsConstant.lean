import AFTD.Prelude

/-!
# nowhere_zero_affine_is_constant

Topic: combinatorics   Node: c8ea02c592b9

Provenance: helper lemma. step towards ternary_minimal_line_cover_minimum_card_eq_hyperplane

If an affine form x ↦ (∑ i, a i * x i) + b on (Fin m → ZMod 3) is nowhere zero, then every coefficient a i is zero.
-/

/-- A nowhere-vanishing affine form on (Fin m → ZMod 3) must have all linear coefficients zero. -/
theorem nowhere_zero_affine_is_constant (m : ℕ) (a : Fin m → ZMod 3) (b : ZMod 3) (h : ∀ x : Fin m → ZMod 3, (∑ i, a i * x i) + b ≠ 0) : ∀ i, a i = 0 := by
  intro i
  by_contra hi
  let x : Fin m → ZMod 3 := Function.update (fun _ => 0) i (-(a i)⁻¹ * b)
  have hx : (∑ j, a j * x j) + b = 0 := by
    have hsum : (∑ j, a j * x j) = a i * (-(a i)⁻¹ * b) := by
      rw [Finset.sum_eq_single i]
      · simp [x]
      · intro j _ hj
        simp [x, hj]
      · intro hnot
        exact absurd (Finset.mem_univ i) hnot
    rw [hsum]
    rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hi]
    ring
  exact h x hx
