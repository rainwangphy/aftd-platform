import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.BrgcWordInjective
import AFTD.Kb.Tcs.BrgcWordInverse
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.Bit

/-!
# brgc_inverse_concat

Topic: combinatorics   Node: 364bd5502ed4

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

The inverse Gray rank of a concatenation has the prefix inverse rank followed by the suffix inverse rank, complemented exactly when the prefix has odd parity.
-/

theorem brgc_aux_inverse_xor (n x y : ℕ) :
    brgc_inverse n (x ^^^ y) = brgc_inverse n x ^^^ brgc_inverse n y := by
  induction n generalizing x y with
  | zero => simp [brgc_inverse]
  | succ n ih =>
    change (x ^^^ y) ^^^ brgc_inverse n ((x ^^^ y) / 2) =
      (x ^^^ brgc_inverse n (x / 2)) ^^^ (y ^^^ brgc_inverse n (y / 2))
    rw [Nat.xor_div_two, ih]
    ac_rfl

theorem brgc_aux_xor_two_mul_add_bit (x y b : ℕ) (hb : b < 2) :
    (2 * x) ^^^ (2 * y + b) = 2 * (x ^^^ y) + b := by
  have hx : 2 * x = Nat.bit false x := by simp [Nat.bit, two_mul]
  have hy : 2 * y + b = Nat.bit (decide (b = 1)) y := by
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp [Nat.bit, two_mul]
  rw [hx, hy, Nat.xor_bit]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp [Nat.bit, two_mul]

theorem brgc_aux_inverse_append_zero {n x : ℕ} (hx : x < 2 ^ n) :
    brgc_inverse (n + 1) (2 * x) =
      2 * brgc_inverse n x + brgc_inverse n x % 2 := by
  rw [brgc_inverse]
  have hd : 2 * x / 2 = x := by omega
  rw [hd]
  let q := brgc_inverse n x
  have hxq : x = q ^^^ (q / 2) := (brgc_word_inverse hx).symm
  have hq : q = 2 * (q / 2) + q % 2 := by omega
  change 2 * x ^^^ q = 2 * q + q % 2
  conv_lhs => rw [hq]
  rw [brgc_aux_xor_two_mul_add_bit _ _ _ (Nat.mod_lt _ (by decide)), hxq,
    Nat.xor_xor_cancel_right]

theorem brgc_aux_inverse_shift (m k a : ℕ) (ha : a < 2 ^ m) :
    brgc_inverse (m + k) (2 ^ k * a) =
      2 ^ k * brgc_inverse m a + (brgc_inverse m a % 2) * (2 ^ k - 1) ∧
    brgc_inverse (m + k) (2 ^ k * a) % 2 = brgc_inverse m a % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hbound : 2 ^ k * a < 2 ^ (m + k) := by
      rw [pow_add]
      nlinarith [Nat.two_pow_pos k]
    have hword : 2 ^ (k + 1) * a = 2 * (2 ^ k * a) := by
      rw [pow_succ]
      ring
    have hexp : m + (k + 1) = (m + k) + 1 := by omega
    rw [hword, hexp, brgc_aux_inverse_append_zero hbound, ih.2, ih.1]
    have hpred : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      rw [pow_succ]
      have := Nat.two_pow_pos k
      omega
    constructor
    · rw [hpred, pow_succ]
      ring
    · have hmod : brgc_inverse m a % 2 < 2 := Nat.mod_lt _ (by decide)
      omega

theorem brgc_aux_xor_high_low (a b k : ℕ) (hb : b < 2 ^ k) :
    (2 ^ k * a) ^^^ b = 2 ^ k * a + b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul_add a hb]
  by_cases hi : k ≤ i
  · have hb' : b.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) hi))
    simp [hi, hb']
  · simp [hi]

theorem brgc_aux_xor_mask_sub {b k : ℕ} (hb : b < 2 ^ k) :
    (2 ^ k - 1) ^^^ b = 2 ^ k - 1 - b := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one]
  have heq : 2 ^ k - 1 - b = 2 ^ k - (b + 1) := by omega
  rw [heq, Nat.testBit_two_pow_sub_succ hb]
  by_cases hi : i < k
  · simp [hi]
  · have hb' : b.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hi)))
    simp [hi, hb']

theorem brgc_aux_inverse_stable {m n x : ℕ} (hm : x < 2 ^ m) (hn : x < 2 ^ n) :
    brgc_inverse m x = brgc_inverse n x := by
  apply brgc_word_injective
  rw [brgc_word_inverse hm, brgc_word_inverse hn]

theorem brgc_aux_concat_bound {m k a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ k) :
    2 ^ k * a + b < 2 ^ (m + k) := by
  rw [pow_add]
  nlinarith [Nat.two_pow_pos k]

theorem brgc_inverse_concat {m k a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ k) :
    brgc_inverse (m + k) (2 ^ k * a + b) =
      2 ^ k * brgc_inverse m a +
        if brgc_inverse m a % 2 = 0 then brgc_inverse k b else 2 ^ k - 1 - brgc_inverse k b := by
  have hb' : b < 2 ^ (m + k) :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))
  rw [← brgc_aux_xor_high_low a b k hb, brgc_aux_inverse_xor, (brgc_aux_inverse_shift m k a ha).1,
    brgc_aux_inverse_stable hb' hb]
  have hir : brgc_inverse k b < 2 ^ k := brgc_inverse_lt_two_pow hb
  rcases Nat.mod_two_eq_zero_or_one (brgc_inverse m a) with hq | hq
  · simp only [hq, zero_mul, add_zero, ite_true]
    exact brgc_aux_xor_high_low _ _ _ hir
  · have hq0 : brgc_inverse m a % 2 ≠ 0 := by omega
    simp only [hq, one_mul, show (1 : ℕ) ≠ 0 by decide, ite_false]
    have hmask : 2 ^ k - 1 < 2 ^ k := by have := Nat.two_pow_pos k; omega
    rw [← brgc_aux_xor_high_low _ _ _ hmask, Nat.xor_assoc, brgc_aux_xor_mask_sub hir,
      brgc_aux_xor_high_low _ _ _ (by omega)]
