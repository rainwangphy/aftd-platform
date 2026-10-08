import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton

/-!
# BooleanAnalysis.flipBit_flipBit

Topic: combinatorics   Node: fcba5fc988dd

Provenance: helper lemma. TCSlib, `BooleanAnalysis.flipBit_flipBit`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Bit-flip is an involution. For a point $x$ in the Boolean hypercube $\{0,1\}^n$ and a coordinate $i$, flipping the
$i$-th coordinate of $x$ twice returns the original point: $(x^i)^i = x$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
@[simp]
lemma BooleanAnalysis.flipBit_flipBit (x : BoolCube n) (i : Fin n) : flipBit (flipBit x i) i = x := by
  ext j
  simp [flipBit, Function.update]
  split_ifs with h
  · subst h; simp
  · rfl
