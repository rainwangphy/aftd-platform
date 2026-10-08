import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInfluence
import AFTD.Kb.Tcs.BooleanAnalysisInfluenceEqSumFourier
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluence
import AFTD.Kb.Tcs.KKLInfluentialCoords

/-!
# KKL.influential_coords_card

Topic: combinatorics   Node: afc3c72c8def

Provenance: helper lemma. TCSlib, `KKL.influential_coords_card`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Few influential coordinates. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function and let $\tau > 0$. The number of
$\tau$-influential coordinates of $f$ — those $i \in [n]$ with $\mathrm{Inf}_i[f] \ge
\tau$ — is bounded by
\[
  \abs{J_\tau(f)} \;\le\; \frac{I[f]}{\tau},
\]
where $I[f] = \sum_{i=1}^n \mathrm{Inf}_i[f]$ is the total influence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.influential_coords_card (f : BooleanFunc n) (τ : ℝ) (hτ : 0 < τ) :
    ((influentialCoords f τ).card : ℝ) ≤ totalInfluence f / τ := by
  rw [le_div_iff₀ hτ]
  calc ((influentialCoords f τ).card : ℝ) * τ
      = (influentialCoords f τ).card • τ := by rw [nsmul_eq_mul]
    _ ≤ ∑ i ∈ influentialCoords f τ, influence i f := by
        apply Finset.card_nsmul_le_sum
        intro i hi
        exact (Finset.mem_filter.mp hi).2
    _ ≤ totalInfluence f := by
        simp only [totalInfluence]
        apply Finset.sum_le_univ_sum_of_nonneg
        intro i
        rw [influence_eq_sum_fourier]
        exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)

-- Step 12: The lowDegreePart restricted to influential coordinates is a junta.
-- More precisely, f_{<=k} depends only on the coordinates appearing in sets S with |S| <= k.
-- We state a simpler version: lowDegreePart is a junta on all n coordinates (trivially).
-- The real content is that we can restrict to influential coords.
