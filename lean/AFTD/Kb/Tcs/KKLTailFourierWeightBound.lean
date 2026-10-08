import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluence
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluenceEqSumSqDeg

/-!
# KKL.tail_fourier_weight_bound

Topic: combinatorics   Node: 837d90a0a07f

Provenance: helper lemma. TCSlib, `KKL.tail_fourier_weight_bound`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Fourier tail weight bound above level $k$. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function, and let $k$ be a positive integer.
Then the total Fourier weight of $f$ carried by frequencies of size strictly greater
than $k$ is bounded by the total influence divided by $k$:
\[
  \sum_{\substack{S \subseteq [n] \\ \abs{S} > k}} \hat f(S)^2 \;\le\; \frac{I[f]}{k}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.tail_fourier_weight_bound (f : BooleanFunc n) (k : ℕ) (hk : 0 < k) :
    (∑ S : Finset (Fin n), if k < S.card then fourierCoeff f S ^ 2 else 0) ≤
    totalInfluence f / k := by
  have hk' : (k : ℝ) > 0 := Nat.cast_pos.mpr hk
  rw [totalInfluence_eq_sum_sq_deg]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro S _
  split_ifs with hS
  · -- k < S.card, so fhat(S)^2 ≤ S.card * fhat(S)^2 / k
    rw [le_div_iff₀ hk']
    have hle : (k : ℝ) ≤ S.card := by exact_mod_cast Nat.le_of_lt hS
    calc fourierCoeff f S ^ 2 * ↑k
        = ↑k * fourierCoeff f S ^ 2 := mul_comm _ _
      _ ≤ ↑S.card * fourierCoeff f S ^ 2 := by
          apply mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  · -- S.card ≤ k, so LHS = 0
    positivity

-- Step 10: Combine steps 08 and 09 to get the L2 approximation theorem.
