import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsAperiodic
import AFTD.Kb.Tcs.BitwordRotate
import AFTD.Kb.Tcs.BitwordRotateIterateCut
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseFlipPreservesCutMax

/-!
# brgc_inverse_flip_preserves_rotation_max

Topic: combinatorics   Node: 306ff27df52f

Provenance: formalization of a published result. Source: Gray-ordered Binary Necklaces (2007), Theorem 3.6, in the equivalent convention of maximal forward Gray rank; the rotation form adds nonconstant-word hypotheses.

Toggling the last bit of an aperiodic nonconstant word that maximizes its inverse Gray rank over all rotations again maximizes that rank, for word length at least two.
-/

theorem brgc_aux_flip_preserves_rotation_max (n x : ℕ) (hn : 2 ≤ n)
    (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1)
    (hy0 : 0 < x ^^^ 1) (hy1 : x ^^^ 1 < 2 ^ n - 1)
    (hap : bitword_is_aperiodic n x)
    (hmax : ∀ r < n, brgc_inverse n ((bitword_rotate n)^[r] x) ≤ brgc_inverse n x) :
    ∀ r < n, brgc_inverse n ((bitword_rotate n)^[r] (x ^^^ 1)) ≤
      brgc_inverse n (x ^^^ 1) := by
  have hx : x < 2 ^ n := by omega
  have hstrict : ∀ a b u v : ℕ, 0 < a → 0 < b → a + b = n →
      u < 2 ^ a → v < 2 ^ b → x = 2 ^ b * u + v →
      brgc_inverse n (2 ^ a * v + u) < brgc_inverse n x := by
    intro a b u v ha hb hab hu hv hsplit
    have ha' : a < n := by omega
    have hrot : (bitword_rotate n)^[a] x = 2 ^ a * v + u := by
      rw [hsplit]
      exact bitword_rotate_iterate_cut hn hab hu hv (by rwa [← hsplit]) (by rwa [← hsplit])
    have hle := hmax a ha'
    rw [hrot] at hle
    by_contra hnot
    have heq : brgc_inverse n (2 ^ a * v + u) = brgc_inverse n x := by omega
    have hbound : 2 ^ a * v + u < 2 ^ n := by
      simpa only [show b + a = n by omega] using brgc_aux_concat_bound hv hu
    have hfix : (bitword_rotate n)^[a] x = x :=
      hrot.trans (brgc_aux_inverse_inj hbound hx heq)
    exact hap a ha ha' hfix
  have hweak := brgc_inverse_flip_preserves_cut_max n x hx hstrict
  intro r hr
  by_cases hr0 : r = 0
  · subst r
    simp
  · let b := n - r
    let u := (x ^^^ 1) / 2 ^ b
    let v := (x ^^^ 1) % 2 ^ b
    have hb : 0 < b := by dsimp [b]; omega
    have hab : r + b = n := by dsimp [b]; omega
    have hu : u < 2 ^ r := by
      apply brgc_aux_word_prefix_bound
      simpa only [hab] using (show x ^^^ 1 < 2 ^ n by omega)
    have hv : v < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hsplit : x ^^^ 1 = 2 ^ b * u + v :=
      (Nat.div_add_mod (x ^^^ 1) (2 ^ b)).symm
    have hrot : (bitword_rotate n)^[r] (x ^^^ 1) = 2 ^ r * v + u := by
      rw [hsplit]
      exact bitword_rotate_iterate_cut hn hab hu hv (by rwa [← hsplit]) (by rwa [← hsplit])
    rw [hrot]
    exact hweak r b u v (by omega) hb hab hu hv hsplit

theorem brgc_aux_rotate_all_ones (n : ℕ) (hn : 0 < n) :
    bitword_rotate n (2 ^ n - 1) = 2 ^ n - 1 := by
  have hp : 2 ^ (n - 1) > 0 := Nat.two_pow_pos _
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    omega
  have hmod : 2 * (2 ^ n - 1) % 2 ^ n = 2 ^ n - 2 := by
    have he : 2 * (2 ^ n - 1) = 2 ^ n + (2 ^ n - 2) := by omega
    rw [he]
    simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hd : (2 ^ n - 1) / 2 ^ (n - 1) = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  simp only [bitword_rotate, hmod, hd]
  omega

theorem brgc_inverse_flip_preserves_rotation_max (n x : ℕ) (hn : 2 ≤ n)
    (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1)
    (hap : bitword_is_aperiodic n x)
    (hmax : ∀ r < n, brgc_inverse n ((bitword_rotate n)^[r] x) ≤ brgc_inverse n x) :
    ∀ r < n, brgc_inverse n ((bitword_rotate n)^[r] (x ^^^ 1)) ≤
      brgc_inverse n (x ^^^ 1) := by
  by_cases hy0 : x ^^^ 1 = 0
  · have hfix : Function.IsFixedPt (bitword_rotate n) (x ^^^ 1) := by
      simp [Function.IsFixedPt, hy0, bitword_rotate]
    intro r hr
    exact le_of_eq (congrArg (brgc_inverse n) (hfix.iterate r))
  by_cases hy1 : x ^^^ 1 = 2 ^ n - 1
  · have hfix : Function.IsFixedPt (bitword_rotate n) (x ^^^ 1) := by
      rw [Function.IsFixedPt, hy1]
      exact brgc_aux_rotate_all_ones n (by omega)
    intro r hr
    exact le_of_eq (congrArg (brgc_inverse n) (hfix.iterate r))
  have hylt : x ^^^ 1 < 2 ^ n :=
    Nat.xor_lt_two_pow (by omega) (Nat.one_lt_two_pow (by omega))
  exact brgc_aux_flip_preserves_rotation_max n x hn hx0 hx1 (by omega) (by omega) hap hmax
