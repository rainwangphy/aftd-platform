import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffChi
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct

/-!
# BooleanAnalysis.innerProduct_chi_self

Topic: combinatorics   Node: 7e6ada9051c9

Provenance: helper lemma. TCSlib, `BooleanAnalysis.innerProduct_chi_self`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Walsh characters have unit norm. Let $n$ be a natural number and let $S \subseteq [n]$. Under the uniform measure on the
Boolean hypercube $\{0,1\}^n$, the Walsh--Fourier character $\chi_S$ satisfies
\[
  \langle \chi_S, \chi_S\rangle \;=\; 2^{-n}\sum_{x\in\{0,1\}^n} \chi_S(x)^2 \;=\; 1.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Self inner product of a Walsh character is `1`. -/
@[simp]
lemma BooleanAnalysis.innerProduct_chi_self (S : Finset (Fin n)) :
    innerProduct (chiS S) (chiS S) = 1 := by
  simp [fourier_coeff_chi]
