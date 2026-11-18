import AFTD.Prelude

/-!
# op861_fourier_pair_identity

Topic: graphs   Node: 25f37f787091

Provenance: helper lemma. Finite character orthogonality, used for op861_ternary_crossing_pairs_dense.

For complex-valued functions f and g on a finite abelian group, the sum over additive characters of the Fourier sum of f times the opposite-frequency Fourier sum of g equals the group order times the sum of the pointwise products f(x)g(x).
-/

open scoped BigOperators

theorem op861_fourier_pair_identity (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f g : G → ℂ) :
    (∑ χ : AddChar G ℂ, (∑ x : G, f x * χ x) * (∑ y : G, g y * χ (-y))) =
      (Fintype.card G : ℂ) * ∑ x : G, f x * g x := by
  classical
  calc
    _ = ∑ χ : AddChar G ℂ, ∑ x : G, ∑ y : G,
        (f x * g y) * χ (x-y) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    _ = ∑ x : G, ∑ y : G, (f x * g y) * ∑ χ : AddChar G ℂ, χ (x-y) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [AddChar.sum_apply_eq_ite]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      simp only [sub_eq_zero, mul_ite, mul_zero]
      rw [Finset.sum_eq_single x]
      · simp
        ring
      · intro y hy hne
        have hne' : x ≠ y := Ne.symm hne
        simp [hne']
      · simp
