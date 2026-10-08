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
import AFTD.Kb.Tcs.G

/-!
# BooleanAnalysis.plancherel

Topic: combinatorics   Node: 6b3d9010f2d4

Provenance: formalization of a published result. Source: Plancherel's identity, as formalized in TCSlib (`BooleanAnalysis.plancherel`). Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Plancherel's identity. Let $f, g : \{0,1\}^n \to \bbr$ be Boolean functions. Then their $L^2$ inner product
with respect to the uniform measure equals the sum, over all subsets $S \subseteq [n]$,
of the products of their corresponding Fourier--Walsh coefficients:
\[
  \langle f, g\rangle \;=\; \sum_{S\subseteq[n]} \hat f(S)\,\hat g(S).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Plancherel's Identity**: `⟪f, g⟫ = ∑_{S ⊆ [n]} f̂(S)ĝ(S)` The sum of the products of Fourier coefficients equals the inner product -/
theorem BooleanAnalysis.plancherel (f g : BooleanFunc n) :
  innerProduct f g = ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S := by
  -- Expand f and g, and use bilinearity + orthonormality
  have expand : innerProduct f g =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        fourierCoeff f S * fourierCoeff g T * innerProduct (chiS S) (chiS T) := by
    -- The exact same expansion logic you used in Parseval, just with `f(x) * g(x)`
    simp_rw [innerProduct, expect, uniformWeight]
    simp_rw [show ∀ x : BoolCube n, f x * g x =
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff g T * chiS T x) from fun x => by
      rw [← walsh_expansion f x, ← walsh_expansion g x]]
    -- ... (Proceed with the exact same Finset sum rearrangement steps from parseval) ...
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
        (∑ T : Finset (Fin n), fourierCoeff g T * chiS T x) =
        ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
          fourierCoeff f S * fourierCoeff g T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
      -- Step 1: move 2⁻¹^n inside x-sum
      rw [Finset.mul_sum]
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n *
          ((∑ S : Finset (Fin n), fourierCoeff f S * chiS S x) *
          (∑ T : Finset (Fin n), fourierCoeff g T * chiS T x)) =
          ∑ x : BoolCube n, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
            (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) from by
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        rw [show (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * ∑ T, fourierCoeff g T * chiS T x) =
            ∑ T, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) from by
          rw [show fourierCoeff f S * chiS S x * ∑ T, fourierCoeff g T * chiS T x =
              ∑ T, fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x) from Finset.mul_sum _ _ _]
          rw [Finset.mul_sum]]]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      -- Step 2c: swap x and T
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro T _
      rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) =
          fourierCoeff f S * fourierCoeff g T * ((2:ℝ)⁻¹^n * ∑ x : BoolCube n, chiS S x * chiS T x) from by
        rw [show ∑ x : BoolCube n, (2:ℝ)⁻¹^n * (fourierCoeff f S * chiS S x * (fourierCoeff g T * chiS T x)) =
            ∑ x : BoolCube n, (fourierCoeff f S * fourierCoeff g T) * ((2:ℝ)⁻¹^n * (chiS S x * chiS T x)) from by
          apply Finset.sum_congr rfl; intro x _; ring]
        rw [← Finset.mul_sum, ← Finset.mul_sum]]]
  rw [expand]
  simp_rw [fourier_coeff_chi, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, if_true]
