import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BrgcWordLtTwoPow
import AFTD.Kb.Tcs.BitwordIsRotationSymmOfNonconstant
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BitwordIsRotation

/-!
# brgc_necklace_first_rank_unique_of_rotation

Topic: combinatorics   Node: 26d63cb15258

Provenance: helper lemma. First occurrences used in OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Two first-occurrence Gray ranks representing the same nonconstant necklace are equal.
-/

theorem brgc_necklace_first_rank_unique_of_rotation (n t u : ℕ) (hn : 2 ≤ n) (ht : brgc_necklace_first_rank n t) (hu : brgc_necklace_first_rank n u) (h : bitword_is_rotation n (brgc_word t) (brgc_word u)) : t = u := by
  rcases lt_trichotomy t u with hlt | heq | hgt
  · exfalso
    have := hu.2.2.2 t hlt
    exact this h
  · exact heq
  · exfalso
    have hx0 : 0 < brgc_word t := Nat.pos_of_ne_zero ht.2.1
    have hx_lt : brgc_word t < 2 ^ n := brgc_word_lt_two_pow ht.1
    have hx1 : brgc_word t < 2 ^ n - 1 := by
      have : brgc_word t ≤ 2 ^ n - 1 := Nat.le_pred_of_lt hx_lt
      exact lt_of_le_of_ne this ht.2.2.1
    have hsymm := bitword_is_rotation_symm_of_nonconstant n (brgc_word t) (brgc_word u) hn hx0 hx1 h
    have := ht.2.2.2 u hgt
    exact this hsymm
