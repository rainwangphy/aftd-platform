import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight

/-!
# BooleanAnalysis.fourierCoeff_empty

Topic: combinatorics   Node: 98ed157c6a81

Provenance: helper lemma. TCSlib, `BooleanAnalysis.fourierCoeff_empty`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Empty-set Fourier coefficient is the mean. Let $f\colon\{0,1\}^n\to\bbr$ be a Boolean function. Then its Fourier–Walsh coefficient
at the empty frequency equals its expectation under the uniform measure:
\[
  \hat f(\varnothing) \;=\; \E[f].
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The Fourier coefficient at `∅` equals the expectation of `f`. -/
lemma BooleanAnalysis.fourierCoeff_empty (f : BooleanFunc n) :
    fourierCoeff f ∅ = expect f := by
  simp [fourierCoeff, innerProduct, chiS, expect, uniformWeight]
