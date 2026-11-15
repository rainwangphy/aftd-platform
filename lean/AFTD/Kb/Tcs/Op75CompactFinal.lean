import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op75_compact_final

Topic: np_completeness   Node: 9c9e09e11842

Provenance: helper lemma. OP-75, arXiv:2610.06092; explicit seven-layer single-pass subset-sum construction.

A width-three layer that forwards the orbit coordinate and computes the two positive parts of the accumulated sum minus the target.
-/

def op75_compact_final (t : ℕ) : ReLUHiddenLayer 3 :=   op75_compact_layer ![![1,0,0],![0,1,0],![0,-1,0]] ![0,-(t:ℚ),(t:ℚ)]
