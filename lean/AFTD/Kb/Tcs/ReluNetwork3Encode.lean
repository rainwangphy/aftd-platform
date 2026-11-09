import AFTD.Prelude
import AFTD.Kb.Tcs.ReluEncodeVec3
import AFTD.Kb.Tcs.ReluEncodeRat
import AFTD.Kb.Tcs.ReluEncodeHiddenLayer3
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# relu_network3_encode

Topic: np_completeness   Node: bf41e33e445e

Provenance: helper lemma. Helper encoding serving OP-75 (arXiv:2610.06092, Remark 5.15). Section 2.1 of the paper writes rational entries as pairs of integers in binary; the bit-level layout is a choice made here.

Encoding of a width-3 ReLU network as a Bool word, of length linear in the total bit length of its rational entries: input weights, input biases, the hidden layers each preceded by true and the list closed by false, output weights, output bias.
-/

def relu_network3_encode (net : ReLUNetwork 3) : List Bool :=
  relu_encode_vec3 net.in_weight ++ relu_encode_vec3 net.in_bias ++
    (net.layers.flatMap (fun l => true :: relu_encode_hidden_layer3 l) ++ [false]) ++
    relu_encode_vec3 net.out_weight ++ relu_encode_rat net.out_bias
