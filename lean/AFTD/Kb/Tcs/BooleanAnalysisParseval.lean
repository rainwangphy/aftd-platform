import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffChi
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf

/-!
# BooleanAnalysis.parseval

Topic: combinatorics   Node: ec445846f798

Provenance: formalization of a published result. Source: Parseval's identity for Boolean functions, as formalized in TCSlib (`BooleanAnalysis.parseval`). Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Parseval's identity for Boolean functions. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function, and equip $\{0,1\}^n$ with the
uniform probability measure. Then the $L^2$ inner product of $f$ with itself equals the
sum of the squares of its Fourier--Walsh coefficients over all subsets $S \subseteq
[n]$:
\[
  \langle f, f\rangle \;=\; \sum_{S \subseteq [n]} \hat f(S)^2.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Parseval's Identity**: `‖f‖² = ∑_{S ⊆ [n]} f̂(S)²`. The sum of squared Fourier coefficients equals the squared `L²` norm. **Source:** [OD14, §1.4]. -/
theorem BooleanAnalysis.parseval (f : BooleanFunc n) :
    innerProduct f f = ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
  -- Expand f = ∑_S f̂(S) χ_S and use bilinearity + orthonormality
  have expand : innerProduct f f =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        fourierCoeff f S * fourierCoeff f T * innerProduct (chiS S) (chiS T) := by
    -- Expand innerProduct and uniformWeight first so f x * f x becomes visible
    simp_rw [innerProduct, expect, uniformWeight]
    -- Now rewrite f(x)*f(x) using walsh_expansion
    simp_rw [show ∀ x : BoolCube n, f x * f x =
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff f T * chiS T x) from fun x => by
      rw [← walsh_expansion f x]]
    -- Goal: 2⁻¹^n * ∑_x (∑_S ...) * (∑_T ...) = ∑_S ∑_T f̂S * f̂T * (2⁻¹^n * ∑_x χSx * χTx)
    -- Use the rearrangement:
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff f T * chiS T x) =
        ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          fourierCoeff f S * fourierCoeff f T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
      -- Step 1: move 2⁻¹^n inside x-sum
      rw [Finset.mul_sum]
      -- Goal: ∑_x 2⁻¹^n * ((∑_S ...) * (∑_T ...)) = ∑_S ∑_T f̂S * f̂T * (...)
      -- Step 2: per x, expand products of sums and collect:
      -- ∑_x 2⁻¹^n * (∑_S ∑_T f̂S * χSx * (f̂T * χTx)) = ∑_S ∑_T f̂S * f̂T * (2⁻¹^n * ∑_x χSx*χTx)
      -- Step 2a: expand per-x product to ∑_x ∑_S ∑_T
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
          ((∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
          (∑ T : Finset (Fin n), fourierCoeff f T * chiS T x)) =
          ∑ x : BoolCube n, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
            (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) from by
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        rw [show (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * ∑ T, fourierCoeff f T * chiS T x) =
            ∑ T, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) from by
          rw [show fourierCoeff f S * chiS S x * ∑ T, fourierCoeff f T * chiS T x =
              ∑ T, fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x) from Finset.mul_sum _ _ _]
          rw [Finset.mul_sum]]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      -- Step 2c: swap x and T
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro T _
      -- Step 2d: factor out f̂S * f̂T
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) =
          fourierCoeff f S * fourierCoeff f T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
        rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff f T * chiS T x)) =
            ∑ x : BoolCube n, (fourierCoeff f S * fourierCoeff f T) * ((2:ℝ)⁻¹^n * (chiS S x * chiS T x)) from by
          apply Finset.sum_congr rfl; intro x _; ring]
        rw [← Finset.mul_sum, ← Finset.mul_sum]]]
  rw [expand]
  simp_rw [fourier_coeff_chi, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl; intro S _; ring
