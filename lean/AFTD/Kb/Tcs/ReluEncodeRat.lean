import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeInt
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# relu_encode_rat

Topic: np_completeness   Node: bd3a5c9d2649

Provenance: helper lemma. Helper encoding serving OP-75 (arXiv:2610.06092, Remark 5.15). Section 2.1 of the paper writes rational entries as pairs of integers in binary; the bit-level layout is a choice made here.

Encoding of a rational in lowest terms as a Bool word: its numerator and denominator in binary.
-/

def relu_encode_rat (q : ℚ) : List Bool :=
  relu_encode_int q.num ++ relu_encode_nat q.den
