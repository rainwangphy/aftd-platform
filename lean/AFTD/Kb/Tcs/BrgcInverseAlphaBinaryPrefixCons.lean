import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaBinaryPrefixBounds
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseWord
import AFTD.Kb.Tcs.BrgcWordLowOnes
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_inverse_alpha_binary_prefix_cons

Topic: combinatorics   Node: f1ae86876e50

Provenance: helper lemma. step towards alpha_lexical_lt_iff_inverse_prefix

The inverse Gray rank of x :: xs equals 2^xs.sum * (2^x - 1) + (2^xs.sum - 1 - brgc_inverse xs.sum (alpha_binary_prefix xs)).
-/

/-- The inverse Gray rank of a cons cell sequence is computed from the prefix block and the tail rank. -/
theorem brgc_inverse_alpha_binary_prefix_cons (x : ℕ) (xs : List ℕ) (hx : 0 < x)
    (hxs : ∀ v ∈ xs, 0 < v) :
    brgc_inverse (x :: xs).sum (alpha_binary_prefix (x :: xs)) =
      2 ^ xs.sum * (2 ^ x - 1) + (2 ^ xs.sum - 1 - brgc_inverse xs.sum (alpha_binary_prefix xs)) := by
  have hcons : alpha_binary_prefix (x :: xs) = 2 ^ xs.sum * 2 ^ (x - 1) + alpha_binary_prefix xs := by
    simp only [alpha_binary_prefix]
    rw [show x - 1 + xs.sum = xs.sum + (x - 1) by omega, pow_add]
  have hfirst : 2 ^ (x - 1) < 2 ^ x := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt : alpha_binary_prefix xs < 2 ^ xs.sum := alpha_binary_prefix_bounds_lt xs hxs
  have hrank : brgc_inverse x (2 ^ (x - 1)) = 2 ^ x - 1 := by
    have hw : brgc_word (2 ^ x - 1) = 2 ^ (x - 1) := by
      have h := brgc_word_low_ones (x - 1)
      rwa [show x - 1 + 1 = x by omega] at h
    rw [← hw]
    exact brgc_inverse_word (by have := Nat.two_pow_pos x; omega)
  have hodd : (2 ^ x - 1) % 2 = 1 := by
    have h2 : 2 ^ x % 2 = 0 := by
      rw [Nat.pow_mod]; simp [Nat.pos_iff_ne_zero.mp hx]
    have hge : 1 ≤ 2 ^ x := Nat.one_le_two_pow
    omega
  rw [hcons, List.sum_cons, brgc_inverse_concat hfirst hlt, hrank, if_neg (by omega)]
