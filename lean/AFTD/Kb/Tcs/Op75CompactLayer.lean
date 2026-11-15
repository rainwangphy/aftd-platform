import AFTD.Prelude
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op75_compact_layer

Topic: np_completeness   Node: e6a9f9085cf1

Provenance: helper lemma. OP-75, arXiv:2610.06092; explicit seven-layer single-pass subset-sum construction.

A width-three hidden layer formed from a rational three-by-three matrix and rational bias vector.
-/

def op75_compact_layer (M : Fin 3 → Fin 3 → ℚ) (b : Fin 3 → ℚ) : ReLUHiddenLayer 3 := ⟨M,b⟩
