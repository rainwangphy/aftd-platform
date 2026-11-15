import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactBlock
import AFTD.Kb.Tcs.ReluEncodeHiddenLayer3
import AFTD.Kb.Tcs.ReluEncodeVec3
import AFTD.Kb.Tcs.ReluEncodeRat
import AFTD.Kb.Tcs.ReluEncodeInt
import AFTD.Kb.Tcs.ReluEncodeNat
import AFTD.Kb.Tcs.Op75BlockTemplatePrefix
import AFTD.Kb.Tcs.Op75BlockTemplateMiddle
import AFTD.Kb.Tcs.Op75BlockTemplateSuffix
import AFTD.Kb.Tcs.ReLUHiddenLayer
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op75_block_encoding_template

Topic: np_completeness   Node: 399560d54ffa

Provenance: helper lemma. OP-75: fixed binary output fragments for the subset-sum to width-three ReLU compiler.

The seven-layer block encoding is a fixed prefix, the positive coefficient encoding, a fixed middle, the negative coefficient encoding, and a fixed suffix.
-/

theorem op75_block_encoding_template (a : ℕ) :
    (op75_compact_block a).flatMap (fun l => true :: relu_encode_hidden_layer3 l) =
      op75_block_template_prefix ++ relu_encode_rat (a : ℚ) ++ op75_block_template_middle ++
        relu_encode_rat (-(a : ℚ)) ++ op75_block_template_suffix := by
  simp [op75_compact_block, op75_compact_layer, relu_encode_hidden_layer3, relu_encode_vec3,
    relu_encode_rat, relu_encode_int, relu_encode_nat, op75_block_template_prefix, op75_block_template_middle,
    op75_block_template_suffix, List.append_assoc] <;> norm_num <;>
    simp [not_lt_of_ge (show (0:ℚ) ≤ (a:ℚ) by positivity),
      not_lt_of_ge (show (0:ℤ) ≤ (a:ℤ) by positivity)]
