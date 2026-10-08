import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInfluence
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluence

/-!
# BooleanAnalysis.max_influence_lower_bound

Topic: combinatorics   Node: 0f89d116755e

Provenance: helper lemma. TCSlib, `BooleanAnalysis.max_influence_lower_bound`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Average influence lower bound. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function on the hypercube of dimension $n\ge 1$.
Then some coordinate carries at least the average influence: there exists an index $i$
with
\[
  \mathrm{Inf}_i[f] \;\ge\; \frac{I[f]}{n},
\]
where $I[f]=\sum_{j=1}^{n}\mathrm{Inf}_j[f]$ is the total influence.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- For any Boolean function `f`, the maximum individual influence is at least the average: `max_i Inf_i[f] ≥ I[f] / n`. -/
lemma BooleanAnalysis.max_influence_lower_bound (f : BooleanFunc n) (hn : 0 < n) :
    ∃ i : Fin n, totalInfluence f / n ≤ influence i f := by
  by_contra h
  push_neg at h
  have hlt : ∀ i : Fin n, influence i f < totalInfluence f / n := h
  have hsum : totalInfluence f = ∑ i : Fin n, influence i f := rfl
  have : totalInfluence f < totalInfluence f := by
    calc totalInfluence f
        = ∑ i : Fin n, influence i f := hsum
      _ < ∑ _i : Fin n, totalInfluence f / n := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
            · intro i _; exact hlt i
      _ = n * (totalInfluence f / n) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ = totalInfluence f := by field_simp
  exact lt_irrefl _ this
