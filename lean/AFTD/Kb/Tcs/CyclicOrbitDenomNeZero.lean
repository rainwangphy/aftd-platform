import AFTD.Prelude

/-!
# cyclic_orbit_denom_ne_zero

Topic: information   Node: 1ded6805ede0

Provenance: helper lemma. arXiv:2611.04947 Lemma 3.2

If x ∈ M has minimal polynomial degree at least 2 over B and a, b, c, d ∈ B satisfy ad - bc ≠ 0, then cx + d ≠ 0 in M.
-/

/-- The denominator cx + d is nonzero when x has degree at least 2 and ad - bc ≠ 0. -/
theorem cyclic_orbit_denom_ne_zero
    {B M : Type*} [Field B] [Field M] [Algebra B M] {x : M}
    (hx : 2 ≤ (minpoly B x).natDegree)
    (a b c d : B) (hdet : a * d - b * c ≠ 0) :
    algebraMap B M c * x + algebraMap B M d ≠ 0 := by
  intro h
  by_cases hc : c = 0
  · subst hc
    simp only [map_zero, zero_mul, zero_add] at h
    have hd : d = 0 := (algebraMap B M).injective (by simpa using h)
    subst hd
    simp at hdet
  · have hc' : algebraMap B M c ≠ 0 := by
      intro h0
      exact hc ((algebraMap B M).injective (by simpa using h0))
    have hx_eq : x = algebraMap B M (-(c⁻¹ * d)) := by
      have hmul : algebraMap B M c * x = - algebraMap B M d := by
        rw [eq_neg_iff_add_eq_zero]
        exact h
      calc
        x = (algebraMap B M c)⁻¹ * (algebraMap B M c * x) := by
            rw [← mul_assoc, inv_mul_cancel₀ hc', one_mul]
        _ = (algebraMap B M c)⁻¹ * (- algebraMap B M d) := by rw [hmul]
        _ = algebraMap B M (-(c⁻¹ * d)) := by
            rw [map_neg, map_mul, map_inv₀]
            ring
    rw [hx_eq] at hx
    have hdeg : (minpoly B (algebraMap B M (-(c⁻¹ * d)))).natDegree = 1 := by
      rw [minpoly.eq_X_sub_C_of_algebraMap_inj (-(c⁻¹ * d)) (algebraMap B M).injective]
      simpa [map_mul] using Polynomial.natDegree_X_add_C (c⁻¹ * d)
    rw [hdeg] at hx
    norm_num at hx
