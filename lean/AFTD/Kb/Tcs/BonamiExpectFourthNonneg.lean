import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BonamiExpectSqNonnegProd

/-!
# Bonami.expect_fourth_nonneg

Topic: combinatorics   Node: ef26b76bdc68

Provenance: helper lemma. TCSlib, `Bonami.expect_fourth_nonneg`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the fourth moment. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function on the Boolean hypercube. Then its
fourth moment under the uniform measure is nonnegative:
\[
  \E\!\left[f^4\right] \;=\; 2^{-n}\sum_{x\in\{0,1\}^n} f(x)^4 \;\ge\; 0.
\]
-/

open BooleanAnalysis in
/-- Shows that the expectation of a fourth power is nonnegative. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.expect_fourth_nonneg {n : ℕ} (f : BooleanFunc n) :
    0 ≤ expect (fun x => f x ^ 4) := by
  convert expect_sq_nonneg_prod (fun x => f x ^ 2) (fun _ => 1) using 1
  norm_num [sq]
  ring_nf
