import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct

/-!
# BooleanAnalysis.fourierCoeff

Topic: combinatorics   Node: 4648ec72a27f

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.fourierCoeff`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{Fourier--Walsh coefficient} of $f$ at frequency $S$ is
\[
  \hat f(S) \;=\; \langle f, \chi_S\rangle
  \;=\; 2^{-n}\sum_{x\in\{0,1\}^n} f(x)\,\chi_S(x).
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The Fourier–Walsh coefficient of `f` at frequency `S`: `f̂(S) = ⟪f, χ_S⟫ = 2⁻ⁿ · ∑_x f(x) · χ_S(x)`. **Source:** [OD14, §1.2]. -/
noncomputable def BooleanAnalysis.fourierCoeff (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  innerProduct f (chiS S)
