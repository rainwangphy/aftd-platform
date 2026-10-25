import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsAperiodicOfPrime
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BitwordRotateIterateSelf
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseWord
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcWordInverse
import AFTD.Kb.Tcs.BitwordIsRotation

/-!
# brgc_necklace_first_rank_min_rotations

Topic: combinatorics   Node: a44070419887

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Every rotation of a first-occurrence representative has inverse Gray rank at least its first-occurrence rank.
-/

theorem brgc_necklace_first_rank_min_rotations {n t : ℕ} (hn : 2 ≤ n)
    (ht : brgc_necklace_first_rank n t) :
    ∀ r < n, t ≤ brgc_inverse n ((bitword_rotate n)^[r] (brgc_word t)) := by
  have hx : brgc_word t < 2 ^ n :=
    Nat.xor_lt_two_pow ht.1 (lt_of_le_of_lt (Nat.div_le_self _ _) ht.1)
  have hx0 : 0 < brgc_word t := Nat.pos_of_ne_zero ht.2.1
  have hx1 : brgc_word t < 2 ^ n - 1 := by have := ht.2.2.1; omega
  have hperiod := bitword_rotate_iterate_self n (brgc_word t) hn hx0 hx1
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp only [Function.iterate_zero, id_eq, brgc_inverse_word ht.1, le_refl]
  · let y := (bitword_rotate n)^[r] (brgc_word t)
    have hylt : y < 2 ^ n := by
      have hh := bitword_is_aperiodic_of_prime_iterate_eq_mod n hn
        (brgc_word t) hx0 hx1 r
      dsimp [y]
      omega
    by_contra hnot
    have hs : brgc_inverse n y < t := Nat.lt_of_not_ge hnot
    apply ht.2.2.2 (brgc_inverse n y) hs
    refine ⟨n - r, by omega, ?_⟩
    rw [brgc_word_inverse hylt]
    change (bitword_rotate n)^[n - r] ((bitword_rotate n)^[r] (brgc_word t)) = _
    rw [← Function.iterate_add_apply, show n - r + r = n by omega, hperiod]
