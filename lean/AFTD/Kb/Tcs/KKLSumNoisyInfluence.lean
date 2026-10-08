import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.KKLNoisyInfluence

/-!
# KKL.sum_noisyInfluence

Topic: combinatorics   Node: 7b12a6d35d9f

Provenance: helper lemma. TCSlib, `KKL.sum_noisyInfluence`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Sum of noisy influences. Fix an integer $n$ and a real number $\rho$, and let $f:\{0,1\}^n\to\bbr$ be a Boolean
function. Summing the noisy influence at noise rate $\rho$ over all coordinates
$i\in[n]$ gives
\[
  \sum_{i=1}^{n} \mathrm{Inf}_i^{\rho}[f]
  \;=\; \sum_{S\subseteq[n]} \abs{S}\,\rho^{\,\abs{S}-1}\,\hat f(S)^2,
\]
where the right-hand sum ranges over all subsets $S$ of $[n]$.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.sum_noisyInfluence (ρ : ℝ) (f : BooleanFunc n) :
    ∑ i : Fin n, noisyInfluence ρ i f =
    ∑ S : Finset (Fin n), S.card * ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 := by
  simp only [noisyInfluence]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

-- Step 03: The total influence is the sum of influences (definitional unfolding).
