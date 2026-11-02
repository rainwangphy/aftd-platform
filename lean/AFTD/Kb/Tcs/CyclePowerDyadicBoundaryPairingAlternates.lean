import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints

/-!
# cycle_power_dyadic_boundary_pairing_alternates

Topic: combinatorics   Node: cea11f93140f

Provenance: helper lemma. RT-1, OP-205, arXiv:2610.15635; auxiliary rigidity lemmas for the dyadic cycle-power covering problem.

In an exact dyadic Boolean class model with exponent at least two, equality of the two boundary bits in every class forces the first inner bit to alternate between successive classes.
-/

theorem cycle_power_dyadic_boundary_pairing_alternates (m : ℕ) (hm : 2 ≤ m) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (h1 : ∀ p : ℤ, x p 1 = x p (2^m-2)) :
    ∀ p : ℤ, x (p+1) 1 = !x p 1 := by
  have hD : 4 ≤ 2^m := by
    calc 4 = 2^2 := by norm_num
      _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
  have ends := cycle_power_dyadic_exact_endpoints m (by omega) x hexact
  intro p
  have e := hexact 1 (by omega) (p + 1)
  simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    sub_zero, Nat.cast_one, add_sub_cancel_right] at e
  rw [show 1 + 2 ^ m - 2 = 2 ^ m - 1 by omega] at e
  simp only [(ends (p + 1)).1, (ends p).2, ← h1 (p + 1), Bool.true_and, Bool.and_true] at e
  revert e
  cases x (p + 1) 1 <;> cases x p 1 <;> decide
