import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInfluenceEqSumFourier
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluence

/-!
# BooleanAnalysis.totalInfluence_eq_sum_sq_deg

Topic: combinatorics   Node: 02305e5e4526

Provenance: formalization of a published result. Source: Total influence via Fourier coefficients, as formalized in TCSlib (`BooleanAnalysis.totalInfluence_eq_sum_sq_deg`). Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Total influence via Fourier coefficients. For every Boolean function $f\colon\{0,1\}^n\to\bbr$, the total influence of $f$ is
recovered from its Fourier--Walsh spectrum by
\[
  I[f] \;=\; \sum_{S\subseteq[n]} \abs{S}\,\hat f(S)^2,
\]
where the sum ranges over all subsets $S$ of $[n]=\{1,\dots,n\}$, $\abs{S}$ is the
cardinality of $S$, and $\hat f(S)$ is the Fourier--Walsh coefficient of $f$ at
frequency $S$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Total Influence via Fourier**: `I[f] = ∑_S |S| · f̂(S)²`. **Source:** [OD14, §2.2]. -/
theorem BooleanAnalysis.totalInfluence_eq_sum_sq_deg (f : BooleanFunc n) :
    totalInfluence f = ∑ S : Finset (Fin n), S.card * fourierCoeff f S ^ 2 := by
  simp only [totalInfluence, influence_eq_sum_fourier]
  rw [Finset.sum_comm]
  congr 1; ext S
  simp [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
