import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffChi
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.KKLLowDegreePart
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit

/-!
# KKL.fourierCoeff_lowDegreePart

Topic: combinatorics   Node: 9c80c8216a0a

Provenance: helper lemma. TCSlib, `KKL.fourierCoeff_lowDegreePart`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Fourier coefficients of the low-degree truncation. Let $f\colon\{0,1\}^n\to\bbr$ be a Boolean function and $k$ a natural number. For every
subset $S\subseteq[n]$, the Fourier--Walsh coefficient of the low-degree part $f_{\le
k}$ at frequency $S$ satisfies
\[
  \widehat{f_{\le k}}(S) \;=\;
  \begin{cases}
    \hat f(S) & \text{if } \abs{S}\le k,\\[2pt]
    0 & \text{if } \abs{S} > k.
  \end{cases}
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.fourierCoeff_lowDegreePart (f : BooleanFunc n) (k : ℕ) (S : Finset (Fin n)) :
    fourierCoeff (lowDegreePart f k) S =
    if S.card ≤ k then fourierCoeff f S else 0 := by
  -- Step 1: Express fourierCoeff of lowDegreePart using linearity
  -- fourierCoeff (lowDegreePart f k) S = innerProduct (lowDegreePart f k) (chiS S)
  -- = expect (fun x => (∑ T, if |T|≤k then fhat(T)*χ_T(x) else 0) * χ_S(x))
  -- = ∑ T, if |T|≤k then fhat(T) * expect (χ_T * χ_S) else 0
  -- = ∑ T, if |T|≤k then fhat(T) * innerProduct χ_T χ_S else 0
  -- = ∑ T, if |T|≤k then fhat(T) * (if T=S then 1 else 0) else 0
  -- = if |S|≤k then fhat(S) else 0
  show fourierCoeff (lowDegreePart f k) S = if S.card ≤ k then fourierCoeff f S else 0
  unfold lowDegreePart
  unfold BooleanAnalysis.fourierCoeff innerProduct expect
  beta_reduce
  -- After unfolding: LHS = uniformWeight n * ∑ x, (∑ T, if T.card ≤ k then fhat_unfolded(T) * χ_T(x) else 0) * χ_S(x)
  -- where fhat_unfolded(T) = uniformWeight n * ∑ y, f y * χ_T y
  -- RHS = if S.card ≤ k then uniformWeight n * ∑ x, f x * χ_S x else 0
  -- We will abbreviate fhat T := uniformWeight n * ∑ y, f y * χ_T y
  set w := uniformWeight n
  set fhat : Finset (Fin n) → ℝ := fun T => w * ∑ y, f y * chiS T y
  -- Now rearrange the LHS
  have step1 : w * ∑ x, (∑ T : Finset (Fin n), if T.card ≤ k then fhat T * chiS T x else 0) * chiS S x =
      ∑ T : Finset (Fin n), if T.card ≤ k then fhat T * (w * ∑ x, chiS T x * chiS S x) else 0 := by
    rw [Finset.mul_sum]
    conv_lhs => arg 2; ext x; rw [Finset.sum_mul]
    simp_rw [show ∀ (T : Finset (Fin n)) (x : BoolCube n),
        (if T.card ≤ k then fhat T * chiS T x else 0) * chiS S x =
        (if T.card ≤ k then fhat T * (chiS T x * chiS S x) else 0) from by
      intros; split_ifs <;> ring]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1; ext T
    split_ifs with hT
    · congr 1; ext x; ring
    · simp
  rw [step1]
  -- Now w * ∑ x, chiS T x * chiS S x = innerProduct (chiS T) (chiS S) (after folding)
  -- But everything is unfolded, so we use fourier_coeff_chi directly
  have ortho : ∀ T : Finset (Fin n),
      w * ∑ x, chiS T x * chiS S x = if T = S then 1 else 0 := by
    intro T
    have := fourier_coeff_chi T S
    simp only [innerProduct, expect] at this
    exact this
  simp_rw [ortho]
  -- Now: ∑ T, if T.card ≤ k then fhat T * (if T = S then 1 else 0) else 0
  --    = if S.card ≤ k then fhat S else 0
  simp only [mul_ite, mul_one, mul_zero]
  -- Goal: ∑ T, if T.card ≤ k then (if T = S then fhat T else 0) else 0
  --     = if S.card ≤ k then w * ∑ x, f x * chiS S x else 0
  -- Collapse nested ifs
  conv_lhs => arg 2; ext T; rw [show (if T.card ≤ k then (if T = S then fhat T else 0) else 0) =
    (if T = S then (if S.card ≤ k then fhat S else 0) else 0) from by
    split_ifs <;> simp_all]
  simp [Finset.sum_ite_eq', fhat]

-- Step 08: The L2 error of low-degree truncation is the tail Fourier weight.
