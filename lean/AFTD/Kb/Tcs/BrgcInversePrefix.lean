import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcWordDivPow
import AFTD.Kb.Tcs.BrgcWordInjective
import AFTD.Kb.Tcs.BrgcWordInverse
import AFTD.Kb.Tcs.BrgcWord

/-!
# brgc_inverse_prefix

Topic: combinatorics   Node: 260851d2e2d6

Provenance: helper lemma. Prefix-parity inverse and supporting arithmetic for OP-392, arXiv:2610.24758, Section 3 and Conjecture 1.

The inverse Gray rank of a high-bit prefix is the corresponding high-bit prefix of the inverse rank.
-/

theorem brgc_inverse_prefix {n k x : ℕ} (hk : k ≤ n) (hx : x < 2 ^ n) :
    brgc_inverse n x / 2 ^ k = brgc_inverse (n - k) (x / 2 ^ k) := by
  have hprefix : x / 2 ^ k < 2 ^ (n - k) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    convert hx using 1
    rw [← pow_add]
    congr 1
    omega
  apply brgc_word_injective
  rw [← brgc_word_div_pow, brgc_word_inverse hx, brgc_word_inverse hprefix]
