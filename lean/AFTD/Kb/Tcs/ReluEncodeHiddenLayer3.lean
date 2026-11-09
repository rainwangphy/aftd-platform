import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeVec3
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# relu_encode_hidden_layer3

Topic: np_completeness   Node: f76627aa503b

Provenance: helper lemma. Helper encoding serving OP-75 (arXiv:2610.06092, Remark 5.15). Section 2.1 of the paper writes rational entries as pairs of integers in binary; the bit-level layout is a choice made here.

Encoding of a width-3 ReLU hidden layer as a Bool word: its 3 by 3 weight matrix row by row, then its bias vector.
-/

def relu_encode_hidden_layer3 (l : ReLUHiddenLayer 3) : List Bool :=
  relu_encode_vec3 (l.weight 0) ++ relu_encode_vec3 (l.weight 1) ++
    relu_encode_vec3 (l.weight 2) ++ relu_encode_vec3 l.bias
