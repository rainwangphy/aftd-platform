import AFTD.Prelude

/-!
# op861_fourier_cube_identity

Topic: graphs   Node: 04cfaff6ba15

Provenance: helper lemma. Finite character orthogonality, used for op861_ternary_crossing_pairs_dense.

For a complex-valued function on a finite abelian group, the sum over all additive characters of the cube of its Fourier sum equals the order of the group times the sum of f(x)f(y)f(−x−y) over ordered pairs x,y.
-/

open scoped BigOperators

theorem op861_fourier_cube_identity (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, (∑ x : G, f x * χ x) ^ 3) =
      (Fintype.card G : ℂ) * ∑ x : G, ∑ y : G, f x * f y * f (-x-y) := by
  classical
  calc
    _ = ∑ χ : AddChar G ℂ, ∑ x : G, ∑ y : G, ∑ z : G,
        (f x * f y * f z) * χ (x+y+z) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [pow_succ, pow_zero, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
      ring
    _ = ∑ x : G, ∑ y : G, ∑ z : G,
        (f x * f y * f z) * ∑ χ : AddChar G ℂ, χ (x+y+z) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [AddChar.sum_apply_eq_ite]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have heq (z : G) : x + y + z = 0 ↔ z = -x-y := by
        rw [add_comm (x+y) z, add_eq_zero_iff_eq_neg]
        simp [sub_eq_add_neg, add_comm]
      simp only [heq, mul_ite, mul_zero]
      rw [Finset.sum_eq_single (-x-y)]
      · simp
        ring
      · intro z hz hne
        simp [hne]
      · simp
