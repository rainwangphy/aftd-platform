import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# BooleanAnalysis.isOddFunc

Topic: combinatorics   Node: 7c59bf22c3fa

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.isOddFunc`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

A Boolean function $f$ is \emph{odd} if $f(\lnot x) = -f(x)$ for all $x$.
This models antisymmetry of pairwise preferences in social choice.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- A Boolean function is **odd** if flipping all inputs negates the output. Models the antisymmetry requirement in social choice. -/
def BooleanAnalysis.isOddFunc (f : BooleanFunc n) : Prop :=
  ∀ x : BoolCube n, f (fun i => !x i) = -f x
