import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_low_ones

Topic: combinatorics   Node: 7231edeeeeae

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

A rank consisting of k+1 low one-bits encodes the word with only bit k set.
-/

theorem brgc_word_low_ones (k : ℕ) :
    brgc_word (2 ^ (k + 1) - 1) = 2 ^ k := by
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hp : 0 < 2 ^ k := Nat.two_pow_pos _
  have hd : (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 := by omega
  unfold brgc_word
  rw [hd]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases hi : i < k
  · have hi' : i < k + 1 := by omega
    have hne : k ≠ i := by omega
    simp [hi, hi', hne]
  · by_cases heq : k = i
    · subst i
      simp
    · have hi' : ¬ i < k + 1 := by omega
      simp [hi, hi', heq]
