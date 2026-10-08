import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# BooleanAnalysis.innerProduct_self_pm_one

Topic: combinatorics   Node: ef9b0f05670e

Provenance: helper lemma. TCSlib, `BooleanAnalysis.innerProduct_self_pm_one`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Self-inner product of a sign function. Let $f : \{0,1\}^n \to \bbr$ be a $\pm 1$-valued Boolean function, so that $f(x) \in
\{-1, 1\}$ for every $x \in \{0,1\}^n$. Then its $L^2$ inner product with itself, taken
with respect to the uniform measure on the cube, equals $1$:
\[
  \langle f, f \rangle \;=\; 2^{-n}\sum_{x \in \{0,1\}^n} f(x)^2 \;=\; 1.
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- For a `±1`-valued function, the `L²` self-inner-product equals `1`. -/
lemma BooleanAnalysis.innerProduct_self_pm_one (f : BooleanFunc n) (hf : isPmOne f) :
    innerProduct f f = 1 := by
  simp only [innerProduct, expect, uniformWeight]
  have hsq : ∀ x : BoolCube n, f x * f x = 1 := fun x => by
    rcases hf x with h | h <;> simp [h]
  simp_rw [hsq]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_pi]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_fin]
  rw [nsmul_eq_mul, mul_one]
  push_cast
  rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
