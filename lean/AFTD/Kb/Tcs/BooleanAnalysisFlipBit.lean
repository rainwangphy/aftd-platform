import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BooleanAnalysis.flipBit

Topic: combinatorics   Node: 6e7af3c4a5ec

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.flipBit`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The point $x^i\in\{0,1\}^n$ obtained from $x$ by flipping the $i$-th coordinate.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Flip the `i`-th bit of `x : {0,1}ⁿ`. -/
def BooleanAnalysis.flipBit (x : BoolCube n) (i : Fin n) : BoolCube n :=
  Function.update x i (!x i)
