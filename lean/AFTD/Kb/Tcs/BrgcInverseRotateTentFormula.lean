import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseWord
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInversePrefix
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BrgcWordDivTwo
import AFTD.Kb.Tcs.BrgcWordLtTwoPow
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.BrgcWordDivPow

/-!
# brgc_inverse_rotate_tent_formula

Topic: combinatorics   Node: e8276b859d7c

Provenance: helper lemma. Arithmetic reformulation of cyclic rotation and the prefix-parity inverse used in OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

In inverse Gray-rank coordinates, cyclic left rotation is the two-branch integer tent map, with the rank parity carried along.
-/

theorem brgc_inverse_rotate_tent_formula (n t : ℕ) (hn : 2 ≤ n) (ht : t < 2 ^ n) : brgc_inverse n (bitword_rotate n (brgc_word t)) = if t < 2 ^ (n - 1) then 2 * t + t % 2 else 2 * (2 ^ n - 1 - t) + t % 2 := by
  split_ifs with hlt
  · have hw : brgc_word t < 2 ^ (n - 1) := brgc_word_lt_two_pow hlt
    have hrot : bitword_rotate n (brgc_word t) = 2 * brgc_word t := by
      dsimp [bitword_rotate]
      have hdiv : brgc_word t / 2 ^ (n - 1) = 0 := Nat.div_eq_of_lt hw
      have h2w : 2 * brgc_word t < 2 ^ n := by
        have : 2 ^ n = 2 * 2 ^ (n - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
          rw [pow_succ', mul_comm]
        omega
      have hmod : 2 * brgc_word t % 2 ^ n = 2 * brgc_word t := Nat.mod_eq_of_lt h2w
      rw [hdiv, hmod, add_zero]
    rw [hrot]
    have hsplit : 2 * brgc_word t = 2 ^ 1 * brgc_word t + 0 := by simp
    have hconcat := @brgc_inverse_concat (n - 1) 1 (brgc_word t) 0 hw (by decide)
    have hnm : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    rw [hnm] at hconcat
    rw [hsplit, hconcat]
    have hinv : brgc_inverse (n - 1) (brgc_word t) = t := brgc_inverse_word hlt
    rw [hinv]
    have hinv0 : brgc_inverse 1 0 = 0 := rfl
    rw [hinv0]
    have hmod2 : t % 2 = 0 ∨ t % 2 = 1 := Nat.mod_two_eq_zero_or_one t
    rcases hmod2 with h0 | h1
    · rw [if_pos h0, h0]
      omega
    · rw [if_neg (by omega), h1]
      omega
  · have ht1 : 2 ^ (n - 1) ≤ t := by omega
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [pow_succ', mul_comm]
    have hb : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
    have ht_sub : t - 2 ^ (n - 1) < 2 ^ (n - 1) := by omega
    have htdiv : t / 2 ^ (n - 1) = 1 := by
      rw [Nat.div_eq_sub_div hb ht1, Nat.div_eq_of_lt ht_sub, zero_add]
    have hdiv : brgc_word t / 2 ^ (n - 1) = 1 := by
      rw [brgc_word_div_pow, htdiv]
      rfl
    have hv : brgc_word t % 2 ^ (n - 1) < 2 ^ (n - 1) := Nat.mod_lt _ hb
    have hrot : bitword_rotate n (brgc_word t) = 2 * (brgc_word t % 2 ^ (n - 1)) + 1 := by
      dsimp [bitword_rotate]
      rw [hdiv]
      have hdecomp : brgc_word t = 2 ^ (n - 1) + brgc_word t % 2 ^ (n - 1) := by
        have h := Nat.div_add_mod (brgc_word t) (2 ^ (n - 1))
        rw [hdiv, mul_one] at h
        exact h.symm
      have h2w : 2 * brgc_word t = 2 ^ n + 2 * (brgc_word t % 2 ^ (n - 1)) := by
        calc 2 * brgc_word t = 2 * (2 ^ (n - 1) + brgc_word t % 2 ^ (n - 1)) := by rw [← hdecomp]
        _ = 2 * 2 ^ (n - 1) + 2 * (brgc_word t % 2 ^ (n - 1)) := by ring
        _ = 2 ^ n + 2 * (brgc_word t % 2 ^ (n - 1)) := by rw [← h2n]
      rw [h2w, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have hconcat1 := @brgc_inverse_concat 1 (n - 1) 1 (brgc_word t % 2 ^ (n - 1)) (by decide) hv
    have h1n : 1 + (n - 1) = n := by omega
    rw [h1n] at hconcat1
    have hsplit1 : brgc_word t = 2 ^ (n - 1) * 1 + brgc_word t % 2 ^ (n - 1) := by
      have h := Nat.div_add_mod (brgc_word t) (2 ^ (n - 1))
      rw [hdiv] at h
      omega
    rw [← hsplit1, brgc_inverse_word ht] at hconcat1
    have hinv1 : brgc_inverse 1 1 = 1 := rfl
    rw [hinv1] at hconcat1
    norm_num at hconcat1
    have hI_lt : brgc_inverse (n - 1) (brgc_word t % 2 ^ (n - 1)) < 2 ^ (n - 1) :=
      brgc_inverse_lt_two_pow hv
    have hI_val : brgc_inverse (n - 1) (brgc_word t % 2 ^ (n - 1)) = 2 ^ n - 1 - t := by
      omega
    have hsplit2 : bitword_rotate n (brgc_word t) = 2 ^ 1 * (brgc_word t % 2 ^ (n - 1)) + 1 := by
      rw [hrot]
      ring
    have hconcat2 := @brgc_inverse_concat (n - 1) 1 (brgc_word t % 2 ^ (n - 1)) 1 hv (by decide)
    have hnm : n - 1 + 1 = n := by omega
    rw [hnm] at hconcat2
    rw [hsplit2, hconcat2]
    rw [hI_val, hinv1]
    have htmod : t % 2 = 0 ∨ t % 2 = 1 := Nat.mod_two_eq_zero_or_one t
    rcases htmod with h0 | h1
    · have hodd : (2 ^ n - 1 - t) % 2 = 1 := by omega
      rw [if_neg (by omega), h0]
      omega
    · have heven : (2 ^ n - 1 - t) % 2 = 0 := by omega
      rw [if_pos heven, h1]
      omega
