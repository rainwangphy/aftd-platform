import AFTD.Prelude
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.Op75CompactBlock
import AFTD.Kb.Tcs.Op75CompactFinal
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op75_compact_network

Topic: np_completeness   Node: 8c0b6492f7c6

Provenance: helper lemma. OP-75, arXiv:2610.06092; explicit seven-layer single-pass subset-sum construction.

The width-three network obtained by concatenating a seven-layer block for each integer weight, followed by the final target-checking layer and an all-one output.
-/

def op75_compact_network (as : List ℕ) (t : ℕ) : ReLUNetwork 3 where
  in_weight := ![1,0,0]
  in_bias := ![0,0,0]
  layers := as.flatMap op75_compact_block ++ [op75_compact_final t]
  out_weight := ![1,1,1]
  out_bias := 0
