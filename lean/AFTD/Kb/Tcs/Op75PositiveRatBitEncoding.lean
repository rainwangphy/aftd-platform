import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeRat
import AFTD.Kb.Tcs.ReluEncodeInt
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_positive_rat_bit_encoding

Topic: np_completeness   Node: f9f00a310fda

Provenance: helper lemma. OP-75: fixed binary output fragments for the subset-sum to width-three ReLU compiler.

The encoding of a nonnegative integer as a rational is its nonnegative sign bit, canonical natural encoding, and denominator-one encoding.
-/

theorem op75_positive_rat_bit_encoding (a : ℕ) :
    relu_encode_rat (a : ℚ) = false :: relu_encode_nat a ++ relu_encode_nat 1 := by
  have ha : ¬ ((a : ℤ) < 0) := by omega
  simp [relu_encode_rat, relu_encode_int, ha]
