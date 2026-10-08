import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisChiSMulChiS
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumChiS
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BooleanAnalysis.fourier_coeff_chi

Topic: combinatorics   Node: 1e1842971815

Provenance: helper lemma. TCSlib, `BooleanAnalysis.fourier_coeff_chi`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Orthonormality of Walsh characters. For any two subsets $S, T \subseteq [n]$, the $L^2$ inner product of the Walsh--Fourier
characters $\chi_S$ and $\chi_T$, taken with respect to the uniform measure on
$\{0,1\}^n$, satisfies
\[
\langle \chi_S, \chi_T\rangle \;=\; \begin{cases} 1 & S = T,\\ 0 & S \neq T. \end{cases}
\]
In particular, the family $\{\chi_S\}_{S\subseteq[n]}$ is orthonormal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Orthonormality**: `⟪χ_S, χ_T⟫ = [S = T]`. The Walsh characters form an orthonormal system in `L²({0,1}ⁿ, uniform)`. **Source:** [OD14, §1.2]. -/
theorem BooleanAnalysis.fourier_coeff_chi (S T : Finset (Fin n)) :
    innerProduct (chiS S) (chiS T) = if S = T then 1 else 0 := by
  simp only [innerProduct, expect, uniformWeight]
  have step : ∑ x : BoolCube n, chiS S x * chiS T x =
      ∑ x : BoolCube n, chiS (symmDiff S T) x := by
    congr 1; ext x; exact chiS_mul_chiS S T x
  rw [step, sum_chiS]
  by_cases hst : S = T
  · -- S = T: symmDiff S T = ∅
    subst hst
    simp only [symmDiff_self, Finset.bot_eq_empty, ↓reduceIte]
    rw [← mul_pow]; norm_num
  · -- S ≠ T: symmDiff S T ≠ ∅
    have hd : symmDiff S T ≠ ∅ := by
      intro h
      apply hst
      have : symmDiff S T = ⊥ := by rwa [Finset.bot_eq_empty]
      exact symmDiff_eq_bot.mp this
    simp [hd, hst]
