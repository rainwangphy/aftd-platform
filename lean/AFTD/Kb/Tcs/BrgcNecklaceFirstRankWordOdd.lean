import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BrgcWordLtTwoPow
import AFTD.Kb.Tcs.BrgcWordDivTwo
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BitwordIsRotation

/-!
# brgc_necklace_first_rank_word_odd

Topic: combinatorics   Node: aecd78fef72c

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

For length at least two, the first nonconstant representative in Gray order has final bit one.
-/

theorem brgc_necklace_first_rank_word_odd {n t : ℕ} (hn : 2 ≤ n)
    (ht : brgc_necklace_first_rank n t) : brgc_word t % 2 = 1 := by
  have htpos : 0 < t := by
    by_contra h
    have : t = 0 := by omega
    exact ht.2.1 (by simp [this, brgc_word])
  have hxlt := brgc_word_lt_two_pow ht.1
  by_contra hodd
  have heven : brgc_word t % 2 = 0 := by omega
  have hsmall : t / 2 < t := Nat.div_lt_self htpos (by omega)
  apply ht.2.2.2 (t / 2) hsmall
  refine ⟨1, by omega, ?_⟩
  simp only [Function.iterate_one]
  rw [bitword_rotate, ← brgc_word_div_two]
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hdouble : 2 * (brgc_word t / 2) = brgc_word t := by omega
  rw [hdouble, Nat.mod_eq_of_lt hxlt]
  have hdiv : brgc_word t / 2 / 2 ^ (n - 1) = 0 := by
    apply Nat.div_eq_of_lt
    omega
  omega
