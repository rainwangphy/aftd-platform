import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcWordInverse
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.BitwordIsRotationSymmOfNonconstant
import AFTD.Kb.Tcs.BitwordIsRotationTransOfNonconstant
import AFTD.Kb.Tcs.BitwordIsAperiodicOfPrime
import AFTD.Kb.Tcs.BrgcNecklaceOrderConsecutiveAperiodicAdjacentNine
import AFTD.Kb.Tcs.BitwordIsRotation
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcWordLtTwoPow
import AFTD.Kb.Tcs.BitwordRotate

/-!
# brgc_necklace_first_rank_exists_of_nonconstant

Topic: combinatorics   Node: 6dc36e1b7416

Provenance: helper lemma. First occurrences used in OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Every nonconstant binary word of length at least two has a first-occurrence Gray rank in its rotation class.
-/

theorem brgc_necklace_first_rank_exists_of_nonconstant_rotate_all_ones (n : ℕ) (hn : 1 ≤ n) :
    bitword_rotate n (2 ^ n - 1) = 2 ^ n - 1 := by
  have h2n : 0 < 2 ^ n := Nat.two_pow_pos n
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc 2 ^ n = 2 ^ (n - 1 + 1) := by rw [show n - 1 + 1 = n by omega]
      _ = 2 ^ (n - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (n - 1) := by ring
  have hpos : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  unfold bitword_rotate
  have h2 : 2 * (2 ^ n - 1) = 2 ^ n + (2 ^ n - 2) := by omega
  have hmod : 2 * (2 ^ n - 1) % 2 ^ n = 2 ^ n - 2 := by
    rw [h2, Nat.add_mod_left]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : (2 ^ n - 1) / 2 ^ (n - 1) = 1 := by
    rw [Nat.div_eq_of_lt_le]
    · omega
    · omega
  rw [hmod, hdiv]
  omega

theorem brgc_necklace_first_rank_exists_of_nonconstant (n x : ℕ) (hn : 2 ≤ n) (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1) : ∃ t, brgc_necklace_first_rank n t ∧ bitword_is_rotation n x (brgc_word t) := by
  classical
  let p : ℕ → Prop := fun s => brgc_word s ≠ 0 ∧ brgc_word s ≠ 2 ^ n - 1 ∧ bitword_is_rotation n x (brgc_word s)
  have hxlt : x < 2 ^ n := by omega
  have hpinv : p (brgc_inverse n x) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [brgc_word_inverse hxlt]; omega
    · rw [brgc_word_inverse hxlt]; omega
    · refine ⟨0, by omega, ?_⟩
      rw [brgc_word_inverse hxlt]
      simp
  have hex : ∃ s, p s := ⟨_, hpinv⟩
  let t := Nat.find hex
  have ht : p t := Nat.find_spec hex
  have htle : t ≤ brgc_inverse n x := Nat.find_min' hex hpinv
  have ht_lt : t < 2 ^ n := by
    have h2 := brgc_inverse_lt_two_pow hxlt
    omega
  refine ⟨t, ?_, ht.2.2⟩
  refine ⟨ht_lt, ht.1, ht.2.1, ?_⟩
  intro s hslt hrot
  have hst : s < 2 ^ n := by omega
  have hsWlt : brgc_word s < 2 ^ n := brgc_word_lt_two_pow hst
  by_cases hs0 : brgc_word s = 0
  · obtain ⟨r, hr, hrr⟩ := hrot
    have h0 : (bitword_rotate n)^[r] 0 = 0 :=
      Function.iterate_fixed (by simp [bitword_rotate]) r
    rw [hs0, h0] at hrr
    exact ht.1 hrr.symm
  · by_cases hs1 : brgc_word s = 2 ^ n - 1
    · obtain ⟨r, hr, hrr⟩ := hrot
      have hfix : bitword_rotate n (2 ^ n - 1) = 2 ^ n - 1 :=
        brgc_necklace_first_rank_exists_of_nonconstant_rotate_all_ones n (by omega)
      have h0 : (bitword_rotate n)^[r] (2 ^ n - 1) = 2 ^ n - 1 :=
        Function.iterate_fixed hfix r
      rw [hs1, h0] at hrr
      exact ht.2.1 hrr.symm
    · have hWs0 : 0 < brgc_word s := Nat.pos_of_ne_zero hs0
      have hWs1 : brgc_word s < 2 ^ n - 1 := by omega
      have hsym : bitword_is_rotation n (brgc_word t) (brgc_word s) :=
        bitword_is_rotation_symm_of_nonconstant n (brgc_word s) (brgc_word t) hn hWs0 hWs1 hrot
      have hxs : bitword_is_rotation n x (brgc_word s) :=
        bitword_is_rotation_trans_of_nonconstant n x (brgc_word t) (brgc_word s) hn hx0 hx1 ht.2.2 hsym
      exact Nat.find_min hex hslt ⟨hs0, hs1, hxs⟩
