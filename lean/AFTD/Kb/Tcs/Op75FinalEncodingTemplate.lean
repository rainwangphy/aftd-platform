import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactFinal
import AFTD.Kb.Tcs.ReluEncodeHiddenLayer3
import AFTD.Kb.Tcs.ReluEncodeVec3
import AFTD.Kb.Tcs.ReluEncodeRat
import AFTD.Kb.Tcs.ReluEncodeInt
import AFTD.Kb.Tcs.ReluEncodeNat
import AFTD.Kb.Tcs.Op75FinalTemplatePrefix
import AFTD.Kb.Tcs.ReLUHiddenLayer
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op75_final_encoding_template

Topic: np_completeness   Node: 008e6748048e

Provenance: helper lemma. OP-75: fixed binary output fragments for the subset-sum to width-three ReLU compiler.

The final target layer encoding is a fixed prefix followed by the negative and positive target coefficient encodings.
-/

theorem op75_final_encoding_template (t : ℕ) :
    true :: relu_encode_hidden_layer3 (op75_compact_final t) =
      op75_final_template_prefix ++ relu_encode_rat (-(t : ℚ)) ++ ([] : List Bool) ++
        relu_encode_rat (t : ℚ) ++ ([] : List Bool) := by
  simp [op75_compact_final, op75_compact_layer, relu_encode_hidden_layer3, relu_encode_vec3,
    relu_encode_rat, relu_encode_int, relu_encode_nat, op75_final_template_prefix, List.append_assoc] <;> norm_num <;> rfl
