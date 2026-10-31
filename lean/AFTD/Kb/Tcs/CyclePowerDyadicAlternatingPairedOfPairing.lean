import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassInnerImpOne
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_alternating_paired_of_pairing

Topic: combinatorics   Node: dfb87163809c

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Reduces the hypothesis of simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_alternating_paired to pairing lemmas of the form of the proved m = 4 lemmas one_iff_fourteen, two_iff_three, ..., twelve_iff_thirteen.

For m ≥ 2, a tight, exactly dyadically covered integer Boolean class model x : ℤ → ℕ → Bool at exponent m with x p 1 = x p (2^m - 2) for every p and the pairings x p (2i) = x p (2i+1) for 1 ≤ i, i + 1 < 2^(m-1), has the alternating-paired structure: x (p+1) 1 = !(x p 1); a class with x p 1 = false has x p j = false for 0 < j < 2^m - 1; a class with x p 1 = true has x p (2j) = x p (2j+1) for every j < 2^(m-1).
-/

theorem cycle_power_dyadic_alternating_paired_of_pairing (m : ℕ) (hm : 2 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (Finset.range (2^m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (h1 : ∀ p : ℤ, x p 1 = x p (2^m - 2))
    (hpr : ∀ p : ℤ, ∀ i, 1 ≤ i → i + 1 < 2^(m-1) → x p (2*i) = x p (2*i+1)) :
    (∀ p : ℤ, x (p+1) 1 = !x p 1) ∧
      (∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^m - 1 → x p j = false) ∧
      (∀ p : ℤ, x p 1 = true → ∀ j < 2^(m-1), x p (2*j) = x p (2*j+1)) := by
  have hD : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hH : 2 ≤ 2 ^ (m - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hends : ∀ v : ℤ, x v 0 = true ∧ x v (2 ^ m - 1) = true := by
    intro v
    have e := hexact 0 (by omega) v
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero,
      zero_add] at e
    revert e
    cases x v 0 <;> cases x v (2 ^ m - 1) <;> decide
  refine ⟨?_, ?_, ?_⟩
  · intro p
    have e := hexact 1 (by omega) (p + 1)
    simp only [pow_one, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
      sub_zero, Nat.cast_one, add_sub_cancel_right] at e
    rw [show 1 + 2 ^ m - 2 = 2 ^ m - 1 by omega] at e
    simp only [(hends (p + 1)).1, (hends p).2, ← h1 (p + 1), Bool.true_and, Bool.and_true] at e
    revert e
    cases x (p + 1) 1 <;> cases x p 1 <;> decide
  · intro p hp j hj0 hj1
    by_contra hne
    have hb : x p j = true := by simpa using hne
    have := cycle_power_dyadic_tight_class_inner_imp_one m hm (x p) (htight p) (h1 p) (hpr p) j hj0 hj1 hb
    rw [hp] at this; exact absurd this (by decide)
  · intro p hp j hj
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; simp only [Nat.mul_zero, zero_add]; rw [hp, (hends p).1]
    rcases (show j + 1 < 2 ^ (m - 1) ∨ j + 1 = 2 ^ (m - 1) by omega) with hlt | heq
    · exact hpr p j h0 hlt
    · rw [show 2 * j = 2 ^ m - 2 by omega, show 2 ^ m - 2 + 1 = 2 ^ m - 1 by omega, ← h1 p, hp,
        (hends p).2]
