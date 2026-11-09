import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeNat

/-!
# relu_encode_int

Topic: np_completeness   Node: 4e46d21d896b

Provenance: helper lemma. Helper encoding serving OP-75 (arXiv:2610.06092, Remark 5.15). Section 2.1 of the paper writes rational entries as pairs of integers in binary; the bit-level layout is a choice made here.

Encoding of an integer as a Bool word: a sign bit followed by the binary encoding of its absolute value.
-/

def relu_encode_int (z : ℤ) : List Bool :=
  decide (z < 0) :: relu_encode_nat z.natAbs
