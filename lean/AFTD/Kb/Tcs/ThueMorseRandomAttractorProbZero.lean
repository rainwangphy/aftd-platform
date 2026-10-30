import AFTD.Prelude
import AFTD.Kb.Tcs.NotIsStringAttractorEmpty
import AFTD.Kb.Tcs.ThueMorseWord
import AFTD.Kb.Tcs.ThueMorseWordLength
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.ThueMorseRandomAttractorProb

/-!
# thue_morse_random_attractor_prob_zero

Topic: combinatorics   Node: 52022bc55400

Provenance: helper lemma. arXiv:2610.10950

For every natural number n, thue_morse_random_attractor_prob n 0 = 0.
-/

/-- The 0-sample random attractor probability of t_n is 0 for every n. -/
theorem thue_morse_random_attractor_prob_zero (n : ℕ) : thue_morse_random_attractor_prob n 0 = 0 := by
  unfold thue_morse_random_attractor_prob
  simp only [pow_zero, div_one]
  have hne : thue_morse_word n ≠ [] := by
    intro h
    have hlen := thue_morse_word_length n
    rw [h] at hlen
    exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos n) hlen.symm
  rw [Nat.cast_eq_zero, Finset.card_eq_zero]
  simp [not_is_string_attractor_empty hne]
