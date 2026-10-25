import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsAperiodicOfPrime
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BitwordRotateIterateCut
import AFTD.Kb.Tcs.BitwordRotateIterateSelf
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.BrgcInversePrefix
import AFTD.Kb.Tcs.BrgcInverseWord
import AFTD.Kb.Tcs.BrgcNecklaceFirstRank
import AFTD.Kb.Tcs.BrgcNecklaceFirstRankMinRotations
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BitwordIsRotation

/-!
# brgc_necklace_first_rank_rotation_max

Topic: combinatorics   Node: 6fc79ba80265

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

Rotating a first-occurrence representative right once gives a representative of maximum inverse Gray rank in its rotation class; the hypothesis that the original representative ends in one is included explicitly.
-/

theorem brgc_aux_inverse_right_one {n x : ℕ} (hn : 0 < n) (hx : x < 2 ^ n) :
    brgc_inverse n (2 ^ (n - 1) + x / 2) =
      2 ^ n - 1 - brgc_inverse n x / 2 := by
  have hp : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hhalf : x / 2 < 2 ^ (n - 1) := by omega
  have hh := brgc_inverse_concat (m := 1) (k := n - 1) (a := 1)
    (by decide : 1 < 2 ^ 1) hhalf
  have hi : brgc_inverse 1 1 = 1 := rfl
  rw [hi] at hh
  simp only [mul_one, Nat.reduceMod, show (1 : ℕ) ≠ 0 by decide, ite_false] at hh
  rw [show 1 + (n - 1) = n by omega] at hh
  rw [hh]
  have hprefix := brgc_inverse_prefix (show 1 ≤ n by omega) hx
  have hprefix' : brgc_inverse n x / 2 = brgc_inverse (n - 1) (x / 2) := by simpa using hprefix
  have hi_bound := brgc_inverse_lt_two_pow hhalf
  omega

theorem brgc_aux_rotate_high {n w : ℕ} (hn : 0 < n) (hw : w < 2 ^ n)
    (hhigh : 2 ^ (n - 1) ≤ w) :
    bitword_rotate n w = 2 * (w - 2 ^ (n - 1)) + 1 := by
  have hp : 0 < 2 ^ (n - 1) := Nat.two_pow_pos _
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hmod : 2 * w % 2 ^ n = 2 * (w - 2 ^ (n - 1)) := by
    have he : 2 * w = 2 ^ n + 2 * (w - 2 ^ (n - 1)) := by omega
    rw [he]
    simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hd : w / 2 ^ (n - 1) = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  simp only [bitword_rotate, hmod, hd]

theorem brgc_necklace_first_rank_rotation_max {n t : ℕ} (hn : 2 ≤ n)
    (ht : brgc_necklace_first_rank n t) (hxodd : brgc_word t % 2 = 1) :
    ∀ r < n,
      brgc_inverse n ((bitword_rotate n)^[r]
        ((bitword_rotate n)^[n - 1] (brgc_word t))) ≤
      brgc_inverse n ((bitword_rotate n)^[n - 1] (brgc_word t)) := by
  have hx : brgc_word t < 2 ^ n :=
    Nat.xor_lt_two_pow ht.1 (lt_of_le_of_lt (Nat.div_le_self _ _) ht.1)
  have hx0 : 0 < brgc_word t := Nat.pos_of_ne_zero ht.2.1
  have hx1 : brgc_word t < 2 ^ n - 1 := by have := ht.2.2.1; omega
  have hperiod := bitword_rotate_iterate_self n (brgc_word t) hn hx0 hx1
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hhalf : brgc_word t / 2 < 2 ^ (n - 1) := by omega
  have hxsplit : brgc_word t = 2 ^ 1 * (brgc_word t / 2) + 1 := by norm_num; omega
  have hz : (bitword_rotate n)^[n - 1] (brgc_word t) =
      2 ^ (n - 1) + brgc_word t / 2 := by
    conv_lhs => rw [hxsplit]
    have hh := bitword_rotate_iterate_cut hn (show n - 1 + 1 = n by omega) hhalf
      (by decide : 1 < 2 ^ 1)
      (show 0 < 2 ^ 1 * (brgc_word t / 2) + 1 by omega)
      (show 2 ^ 1 * (brgc_word t / 2) + 1 < 2 ^ n - 1 by rwa [← hxsplit])
    simpa using hh
  have hzr : brgc_inverse n ((bitword_rotate n)^[n - 1] (brgc_word t)) =
      2 ^ n - 1 - t / 2 := by
    rw [hz, brgc_aux_inverse_right_one (by omega) hx, brgc_inverse_word ht.1]
  have htr : t / 2 < 2 ^ (n - 1) := by have htt := ht.1; omega
  have hlowrank : 2 ^ (n - 1) ≤
      brgc_inverse n ((bitword_rotate n)^[n - 1] (brgc_word t)) := by omega
  intro r hr
  let w := (bitword_rotate n)^[r] ((bitword_rotate n)^[n - 1] (brgc_word t))
  have hw : w < 2 ^ n := by
    have hh := bitword_is_aperiodic_of_prime_iterate_eq_mod n hn
      (brgc_word t) hx0 hx1 (r + (n - 1))
    dsimp [w]
    rw [← Function.iterate_add_apply]
    omega
  by_cases hwh : w < 2 ^ (n - 1)
  · have hstable : brgc_inverse n w = brgc_inverse (n - 1) w := brgc_aux_inverse_stable hw hwh
    have hwrank : brgc_inverse n w < 2 ^ (n - 1) := by rw [hstable]; exact brgc_inverse_lt_two_pow hwh
    change brgc_inverse n w ≤ _
    omega
  · have hv : bitword_rotate n w = (bitword_rotate n)^[r] (brgc_word t) := by
      dsimp [w]
      rw [← Function.iterate_add_apply,
        ← Function.iterate_succ_apply' (bitword_rotate n) (r + (n - 1)) (brgc_word t),
        show (r + (n - 1)).succ = r + n by omega,
        Function.iterate_add_apply, hperiod]
    have hvbound : bitword_rotate n w < 2 ^ n := by
      have hh := bitword_is_aperiodic_of_prime_iterate_eq_mod n hn
        (brgc_word t) hx0 hx1 r
      rw [hv]
      omega
    have hmin : t ≤ brgc_inverse n (bitword_rotate n w) := by
      rw [hv]
      exact brgc_necklace_first_rank_min_rotations hn ht r hr
    have hwexpr : w = 2 ^ (n - 1) + bitword_rotate n w / 2 := by
      rw [brgc_aux_rotate_high (by omega) hw (by omega)]
      omega
    change brgc_inverse n w ≤ _
    rw [hwexpr, brgc_aux_inverse_right_one (by omega) hvbound, hzr]
    exact Nat.sub_le_sub_left (Nat.div_le_div_right hmin) _
