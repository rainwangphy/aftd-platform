import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisSumChiSMulEq

/-!
# BooleanAnalysis.walsh_expansion

Topic: combinatorics   Node: 06dd2c0ee0a8

Provenance: helper lemma. TCSlib, `BooleanAnalysis.walsh_expansion`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Walsh–Fourier expansion of a Boolean function. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function of arity $n$. Then at every point
$x\in\{0,1\}^n$,
\[
  f(x) \;=\; \sum_{S\subseteq[n]} \hat f(S)\,\chi_S(x),
\]
where the sum ranges over all subsets $S$ of $[n]$, $\chi_S$ is the Walsh character of
$S$, and $\hat f(S)=\langle f,\chi_S\rangle$ is the Fourier–Walsh coefficient of $f$ at
$S$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Walsh Expansion**: every Boolean function `f : {0,1}ⁿ → ℝ` can be written as `f(x) = ∑_{S ⊆ [n]} f̂(S) · χ_S(x)`. This is the Fourier inversion formula for the uniform measure on `{0,1}ⁿ`. **Source:** [OD14, §1.3]. -/
theorem BooleanAnalysis.walsh_expansion (f : BooleanFunc n) (x : BoolCube n) :
    f x = ∑ S : Finset (Fin n), fourierCoeff f S * chiS S x := by
  simp only [fourierCoeff, innerProduct, expect, uniformWeight]
  -- Goal: f x = ∑_S (2⁻ⁿ * ∑_y f(y) * χ_S(y)) * χ_S(x)
  -- Proof: show both sides equal 2⁻ⁿ * ∑_y f(y) * ∑_S χ_S(y) * χ_S(x)
  --        then use the completeness kernel
  symm
  calc ∑ S : Finset (Fin n), ((2:ℝ)⁻¹^n * ∑ y, f y * chiS S y) * chiS S x
      = (2:ℝ)⁻¹^n * ∑ y : BoolCube n, ∑ S : Finset (Fin n), f y * (chiS S y * chiS S x) := by
        -- Move 2⁻¹^n outside by rearranging: ∑_S (a * b_S) * c_S = a * ∑_S b_S * c_S,
        -- then swap sum order and distribute f y
        have step1 : ∑ S : Finset (Fin n), ((2:ℝ)⁻¹^n * ∑ y, f y * chiS S y) * chiS S x =
            (2:ℝ)⁻¹^n * ∑ S : Finset (Fin n), (∑ y, f y * chiS S y) * chiS S x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro S _; ring
        have step2 : ∑ S : Finset (Fin n), (∑ y, f y * chiS S y) * chiS S x =
            ∑ y : BoolCube n, ∑ S : Finset (Fin n), f y * (chiS S y * chiS S x) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro y _
          apply Finset.sum_congr rfl; intro S _; ring
        rw [step1, step2]
    _ = (2:ℝ)⁻¹^n * ∑ y : BoolCube n, f y * (∑ S, chiS S y * chiS S x) := by
        congr 1
        apply Finset.sum_congr rfl; intro y _
        rw [← Finset.mul_sum]
    _ = (2:ℝ)⁻¹^n * ∑ y : BoolCube n, f y * (if y = x then (2:ℝ)^n else 0) := by
        simp_rw [sum_chiS_mul_eq]
    _ = (2:ℝ)⁻¹^n * (f x * (2:ℝ)^n) := by
        congr 1
        simp [Finset.sum_ite_eq', Finset.mem_univ]
    _ = f x := by
        rw [← mul_assoc, mul_comm ((2:ℝ)⁻¹^n) (f x), mul_assoc, ← mul_pow,
            inv_mul_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_pow, mul_one]
