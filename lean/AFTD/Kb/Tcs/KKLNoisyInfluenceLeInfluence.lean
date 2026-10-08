import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInfluence
import AFTD.Kb.Tcs.BooleanAnalysisInfluenceEqSumFourier
import AFTD.Kb.Tcs.KKLNoisyInfluence

/-!
# KKL.noisyInfluence_le_influence

Topic: combinatorics   Node: ec6ca74975c2

Provenance: helper lemma. TCSlib, `KKL.noisyInfluence_le_influence`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Noisy influence is dominated by influence. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function, let $i\in[n]$ be a coordinate, and let
$\rho\in\bbr$ satisfy $0\le\rho\le 1$. Then the noisy influence of $i$ on $f$ at noise
rate $\rho$ is at most the influence of $i$ on $f$:
\[
  \mathrm{Inf}_i^{\rho}[f]\;\le\;\mathrm{Inf}_i[f].
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.noisyInfluence_le_influence (i : Fin n) (f : BooleanFunc n)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    noisyInfluence ρ i f ≤ influence i f := by
  rw [noisyInfluence, influence_eq_sum_fourier]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hiS
  · exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hρ0 hρ1)
  · exact le_refl _

-- Step 14: For rho in (0,1), noisy influence can be bounded using
-- Inf_i^rho[f] <= (Inf_i[f])^{1-rho} ... actually we use a simpler bound.
-- Key lemma: Inf_i^rho[f] <= Inf_i[f]^rho (by log-convexity / power mean).
-- This is a nontrivial step; we state a weaker but sufficient version.
