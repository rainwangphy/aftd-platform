import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect

/-!
# Bonami.expect_sq_nonneg

Topic: combinatorics   Node: 9a71d2187f62

Provenance: helper lemma. TCSlib, `Bonami.expect_sq_nonneg`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the mean square. For every Boolean function $f : \{0,1\}^n \to \bbr$, the expectation of $f^2$ under the
uniform measure is nonnegative: $0 \le \E[f^2]$, where $\E[f^2] =
2^{-n}\sum_{x\in\{0,1\}^n} f(x)^2$.
-/

open BooleanAnalysis in
/-- Shows that the expectation of a square is nonnegative. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.expect_sq_nonneg {n : ℕ} (f : BooleanFunc n) :
    0 ≤ expect (fun x => f x ^ 2) := by
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
