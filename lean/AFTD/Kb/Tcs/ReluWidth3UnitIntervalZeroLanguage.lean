import AFTD.Prelude
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero
import AFTD.Kb.Tcs.ReLUNetwork

/-!
# relu_width3_unit_interval_zero_language

Topic: np_completeness   Node: 688232db7c01

Provenance: formalization of a published result. Source: arXiv:2610.06092 (Fractal Gadgets for Neural Networks: The Complexity of the Narrow Regime), Section 2.1 (network representation: rational entries as pairs of integers written in binary) and Remark 5.15. The bit-level layout is a choice made here; the paper fixes only binary numerators and denominators.

The verification language at width 3 on the unit interval, for the fixed encoding relu_network3_encode: the set of Bool words w such that w = relu_network3_encode net for some width-3 feedforward ReLU network net with rational weights and biases (ReLUNetwork 3) that has a zero in [0, 1] (relu_network_has_unit_interval_zero net).
-/

def relu_width3_unit_interval_zero_language : Language Bool :=
  {w | ∃ net : ReLUNetwork 3, relu_network3_encode net = w ∧
    relu_network_has_unit_interval_zero net}
