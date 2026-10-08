import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFlipBit

/-!
# BooleanAnalysis.influence

Topic: combinatorics   Node: 4abbe5fff403

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.influence`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{influence} of coordinate $i$ on $f$ measures how often flipping
bit $i$ changes the output:
\[
  \mathrm{Inf}_i[f]
  \;=\; \E\!\left[\frac{(f(x)-f(x^i))^2}{4}\right].
\]
For $\pm 1$-valued $f$ this equals $\Pr[f(x)\ne f(x^i)]$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The **influence** of coordinate `i` on `f`: `Inf_i[f] = Pr_x[f(x) ≠ f(xⁱ)]` where `xⁱ` denotes `x` with the `i`-th bit flipped. For `{-1,1}`-valued functions this equals `𝔼[(f(x) - f(xⁱ))² / 4]`. **Source:** [OD14, §2.1]. -/
noncomputable def BooleanAnalysis.influence (i : Fin n) (f : BooleanFunc n) : ℝ :=
  expect (fun x ↦ (f x - f (flipBit x i)) ^ 2 / 4)
