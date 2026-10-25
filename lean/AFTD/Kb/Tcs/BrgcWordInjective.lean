import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcWordXor
import AFTD.Kb.Tcs.BrgcWordEqZeroIff
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_word_injective

Topic: combinatorics   Node: 44d678d2e829

Provenance: helper lemma. Supporting arithmetic and canonical-representative lemmas for OP-392, arXiv:2610.24758, Conjecture 1.

Binary reflected Gray encoding is injective on natural numbers.
-/

theorem brgc_word_injective : Function.Injective brgc_word := by
  intro t u h
  apply Nat.eq_of_xor_eq_zero
  apply (brgc_word_eq_zero_iff _).mp
  rw [brgc_word_xor, h, Nat.xor_self]
