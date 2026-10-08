import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight

/-!
# BooleanAnalysis.expect

Topic: combinatorics   Node: 0d5cccb975aa

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.expect`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{expectation} of $f$ under the uniform measure:
\[
  \E[f] \;=\; 2^{-n}\sum_{x\in\{0,1\}^n} f(x).
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Expectation of `f` under the uniform measure on `{0,1}ⁿ`. `𝔼[f] = 2⁻ⁿ · ∑_{x ∈ {0,1}ⁿ} f(x)`. **Source:** [OD14, §1.1]. -/
noncomputable def BooleanAnalysis.expect (f : BooleanFunc n) : ℝ :=
  uniformWeight n * ∑ x : BoolCube n, f x
