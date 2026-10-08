import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductSelfPmOne
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne
import AFTD.Kb.Tcs.BooleanAnalysisParseval

/-!
# BooleanAnalysis.parseval_pm_one

Topic: combinatorics   Node: 8c058cb1c8a3

Provenance: helper lemma. TCSlib, `BooleanAnalysis.parseval_pm_one`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Parseval's identity for $\pm 1$-valued functions. Let $f \colon \{0,1\}^n \to \bbr$ be a Boolean function that is $\pm 1$-valued, meaning
$f(x) \in \{-1,1\}$ for every $x \in \{0,1\}^n$. Then its Fourier--Walsh coefficients
satisfy
\[
  \sum_{S \subseteq [n]} \hat f(S)^2 \;=\; 1,
\]
the sum ranging over all subsets $S$ of $[n]$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Parseval for `±1`-valued functions**: `∑_S f̂(S)² = 1`. -/
lemma BooleanAnalysis.parseval_pm_one (f : BooleanFunc n) (hf : isPmOne f) :
    ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1 := by
  rw [← parseval, innerProduct_self_pm_one f hf]
