import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect

/-!
# BooleanAnalysis.innerProduct

Topic: combinatorics   Node: 93b7a5dcf8cd

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.innerProduct`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{$L^2$ inner product} of two Boolean functions with respect to the
uniform measure:
\[
  \langle f, g\rangle \;=\; \E[f\cdot g]
  \;=\; 2^{-n}\sum_{x\in\{0,1\}^n} f(x)\,g(x).
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The `L²` inner product on Boolean functions with respect to the uniform measure: `⟪f, g⟫ = 𝔼[f · g] = 2⁻ⁿ · ∑_x f(x) g(x)`. **Source:** [OD14, §1.2]. -/
noncomputable def BooleanAnalysis.innerProduct (f g : BooleanFunc n) : ℝ :=
  expect (fun x ↦ f x * g x)
