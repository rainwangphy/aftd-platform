import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfModel

/-!
# cycle_power_dyadic_alternating_half_crossed_cover

Topic: combinatorics   Node: d3fa08e1fdb9

Provenance: helper lemma. RT-1 / OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-08: the alignment lemma cycle_power_dyadic_no_island_of_alternating_halves reduced to the pairing of the two half models, which experiment 18632 finds forced already inside the span of one class.

Crossed coverage of the half models. In an integer Boolean class model at exponent m+1 in which every distance 1 ≤ d < 2^(m+1) is covered, bit 1 alternates (x (p+1) 1 = !x p 1) and every class without bit 1 has no inner bit, fix a root s with bit 1. Then for every 1 ≤ j < m and every v there is a < 2^j such that the class rooted at 2(v-a)+s contains the even offset 2a and the odd offset 2(a+2^m-2^j)+1, and there is a < 2^j such that it contains the odd offset 2a+1 and the even offset 2(a+2^m-2^j). These are the covers of the odd distances 2^(m+1)-2^(j+1)±1; in half-model terms (y q b = x (2q+s) (2b), z q b = x (2q+s) (2b+1)) they are the mixed pairs y–z and z–y at the dyadic distance 2^m-2^j.
-/

theorem cycle_power_dyadic_alternating_half_crossed_cover (m : ℕ) (x : ℤ → ℕ → Bool)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(m+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(m+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (s : ℤ) (hs : x s 1 = true) :
    ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      (∃ a : ℕ, a < 2^j ∧ x (2*(v-(a : ℤ))+s) (2*a) = true ∧
        x (2*(v-(a : ℤ))+s) (2*(a+2^m-2^j)+1) = true) ∧
      (∃ a : ℕ, a < 2^j ∧ x (2*(v-(a : ℤ))+s) (2*a+1) = true ∧
        x (2*(v-(a : ℤ))+s) (2*(a+2^m-2^j)) = true) := by
  intro j hj1 hjm v
  have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt s hs
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  have hjpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
  have hj2 : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj1
  have hjm2 : 2 ^ (j + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hjm
  constructor
  · -- the pair (2v+s, 2v+s + 2(2^m-2^j)+1)
    obtain ⟨a, ha, h1, h2⟩ := hcover (2 * (2 ^ m - 2 ^ j) + 1) (by omega) (by omega) (2 * v + s)
    rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩
    · refine ⟨a', by omega, ?_, ?_⟩
      · have hr : 2 * v + s - ((2 * a' : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
        rw [hr] at h1; exact h1
      · have hr : 2 * v + s - ((2 * a' : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
        rw [hr, show 2 * a' + (2 * (2 ^ m - 2 ^ j) + 1) = 2 * (a' + 2 ^ m - 2 ^ j) + 1 by omega] at h2
        exact h2
    · exfalso
      have hr : 2 * v + s - ((2 * a' + 1 : ℕ) : ℤ) = 2 * (v - a' - 1) + s + 1 := by
        push_cast; ring
      rw [hr] at h1
      rw [hend _ (hpar _).2 (2 * a' + 1) (by omega) (by omega)] at h1
      exact Bool.false_ne_true h1
  · -- the pair (2v+s+1, 2v+s+1 + 2(2^m-2^j)-1)
    obtain ⟨a, ha, h1, h2⟩ := hcover (2 * (2 ^ m - 2 ^ j) - 1) (by omega) (by omega) (2 * v + s + 1)
    rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩
    · exfalso
      have hr : 2 * v + s + 1 - ((2 * a' : ℕ) : ℤ) = 2 * (v - a') + s + 1 := by push_cast; ring
      rw [hr] at h1 h2
      rcases Nat.eq_zero_or_pos a' with h0 | h0
      · subst h0
        rw [hend _ (hpar _).2 (2 * 0 + (2 * (2 ^ m - 2 ^ j) - 1)) (by omega) (by omega)] at h2
        exact Bool.false_ne_true h2
      · rw [hend _ (hpar _).2 (2 * a') (by omega) (by omega)] at h1
        exact Bool.false_ne_true h1
    · refine ⟨a', by omega, ?_, ?_⟩
      · have hr : 2 * v + s + 1 - ((2 * a' + 1 : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
        rw [hr] at h1; exact h1
      · have hr : 2 * v + s + 1 - ((2 * a' + 1 : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
        rw [hr, show 2 * a' + 1 + (2 * (2 ^ m - 2 ^ j) - 1) = 2 * (a' + 2 ^ m - 2 ^ j) by omega] at h2
        exact h2
