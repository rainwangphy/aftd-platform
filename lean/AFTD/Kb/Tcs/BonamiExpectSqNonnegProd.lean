import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect

/-!
# Bonami.expect_sq_nonneg_prod

Topic: combinatorics   Node: d9ddb7d339bf

Provenance: helper lemma. TCSlib, `Bonami.expect_sq_nonneg_prod`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the expectation of a product of squares. For any two Boolean functions $g, h : \{0,1\}^n \to \bbr$, the expectation of the
product of their squares under the uniform measure is nonnegative:
\[
\E\!\left[\,g^2\, h^2\,\right] \;=\; 2^{-n} \sum_{x \in \{0,1\}^n} g(x)^2\, h(x)^2
\;\ge\; 0.
\]
-/

open BooleanAnalysis in
/-- Shows that the expectation of a product of squares is nonnegative. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.expect_sq_nonneg_prod {n : ℕ} (g h : BooleanFunc n) :
    0 ≤ expect (fun x => g x ^ 2 * h x ^ 2) := by
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg fun _ _ => by positivity)
