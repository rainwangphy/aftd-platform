import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op75_compact_block

Topic: np_completeness   Node: 830395274347

Provenance: helper lemma. OP-75, arXiv:2610.06092; explicit seven-layer single-pass subset-sum construction.

Seven width-three hidden layers for one nonnegative integer weight in the one-pass subset-sum construction.
-/

def op75_compact_block (a : ℕ) : List (ReLUHiddenLayer 3) :=   [ op75_compact_layer ![![1,0,0],![0,1,0],![4,0,0]] ![0,0,-1],
    op75_compact_layer ![![1,0,0],![0,1,(a:ℚ)],![4,0,0]] ![0,0,-2],
    op75_compact_layer ![![1,0,0],![0,1,-(a:ℚ)],![0,0,0]] ![0,0,0],
    op75_compact_layer ![![1,0,0],![0,1,0],![8,0,0]] ![0,0,-6],
    op75_compact_layer ![![1,0,0],![0,1,0],![8,0,-1]] ![0,0,-3],
    op75_compact_layer ![![1,0,0],![0,1,0],![-4,0,1]] ![0,0,1],
    op75_compact_layer ![![0,0,-1],![0,1,0],![0,0,0]] ![1,0,0] ]
