import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeRat
import AFTD.Kb.Tcs.ReluEncodeInt
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# op75_negative_rat_bit_encoding

Topic: np_completeness   Node: b56bd776d4d8

Provenance: helper lemma. OP-75: fixed binary output fragments for the subset-sum to width-three ReLU compiler.

The encoding of the negative of a nonnegative integer has sign bit set exactly when that integer is nonzero, followed by its canonical natural encoding and denominator-one encoding.
-/

theorem op75_negative_rat_bit_encoding (a : ℕ) :
    relu_encode_rat (-(a : ℚ)) = decide (0 < a) :: relu_encode_nat a ++ relu_encode_nat 1 := by
  simp [relu_encode_rat, relu_encode_int]
