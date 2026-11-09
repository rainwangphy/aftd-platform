import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeRat

/-!
# relu_encode_vec3

Topic: np_completeness   Node: 23437ea9e11b

Provenance: helper lemma. Helper encoding serving OP-75 (arXiv:2610.06092, Remark 5.15). Section 2.1 of the paper writes rational entries as pairs of integers in binary; the bit-level layout is a choice made here.

Encoding of a rational vector of length 3 as the concatenation of the encodings of its three entries.
-/

def relu_encode_vec3 (v : Fin 3 → ℚ) : List Bool :=
  relu_encode_rat (v 0) ++ relu_encode_rat (v 1) ++ relu_encode_rat (v 2)
