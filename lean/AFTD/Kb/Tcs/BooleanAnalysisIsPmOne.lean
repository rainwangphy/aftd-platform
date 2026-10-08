import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# BooleanAnalysis.isPmOne

Topic: combinatorics   Node: bbd63196856b

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.isPmOne`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

$f$ is \emph{$\pm 1$-valued} if $f(x)\in\{-1,1\}$ for all $x$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- A Boolean function takes values in `{-1, 1}`. -/
def BooleanAnalysis.isPmOne (f : BooleanFunc n) : Prop :=
  ∀ x : BoolCube n, f x = 1 ∨ f x = -1
