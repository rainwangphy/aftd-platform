import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeffChi
import AFTD.Kb.Tcs.BooleanAnalysisInfluence
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisParseval
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion
import AFTD.Kb.Tcs.BooleanAnalysisChiSFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.G

/-!
# BooleanAnalysis.influence_eq_sum_fourier

Topic: combinatorics   Node: 552acf853f6c

Provenance: helper lemma. TCSlib, `BooleanAnalysis.influence_eq_sum_fourier`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Influence via Fourier coefficients. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function and fix a coordinate $i\in[n]$. Then the
influence of $i$ on $f$ equals the sum of the squared Fourier--Walsh coefficients over
all frequencies containing $i$:
\[
  \mathrm{Inf}_i[f] \;=\; \sum_{\substack{S\subseteq[n]\\ i\in S}} \hat f(S)^2.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- **Influence via Fourier**: `Inf_i[f] = ∑_{S ∋ i} f̂(S)²`. **Source:** [OD14, §2.2]. -/
theorem BooleanAnalysis.influence_eq_sum_fourier (i : Fin n) (f : BooleanFunc n) :
    influence i f = ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S ^ 2 else 0 := by
  -- Key: f(x) - f(flipBit x i) = 2 * ∑_{S∋i} f̂(S) * χ_S(x)
  have key : ∀ x : BoolCube n,
      f x - f (flipBit x i) =
      2 * ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S * chiS S x else 0 := by
    intro x
    rw [show f x = ∑ S, fourierCoeff f S * chiS S x from walsh_expansion f x,
        show f (flipBit x i) = ∑ S, fourierCoeff f S * chiS S (flipBit x i) from walsh_expansion f _,
        ← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, chiS_flipBit]
    -- Goal: ∑ S, f̂(S) * (χ_S(x) - if i∈S then -χ_S(x) else χ_S(x)) = 2 * ∑_{S∋i} f̂(S)*χ_S(x)
    trans (∑ S : Finset (Fin n), if i ∈ S then 2 * (fourierCoeff f S * chiS S x) else 0)
    · apply Finset.sum_congr rfl; intro S _
      by_cases hiS : i ∈ S <;> simp [hiS, two_mul]
      ring
    · rw [show ∑ S : Finset (Fin n), (if i ∈ S then 2 * (fourierCoeff f S * chiS S x) else 0) =
          2 * ∑ S : Finset (Fin n), if i ∈ S then fourierCoeff f S * chiS S x else 0 from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro S _
        split_ifs <;> ring]
  -- Define g(x) = ∑_{S∋i} f̂(S) * χ_S(x)
  -- influence i f = 𝔼[(2g(x))²/4] = 𝔼[g(x)²] = innerProduct g g = ∑_{S∋i} f̂(S)² by Parseval
  simp only [influence, expect, uniformWeight]
  simp_rw [key]
  simp_rw [show ∀ x : BoolCube n,
      (2 * ∑ S, if i ∈ S then fourierCoeff f S * chiS S x else 0) ^ 2 / 4 =
      (∑ S, if i ∈ S then fourierCoeff f S * chiS S x else 0) ^ 2 from fun x => by ring]
  -- Rewrite as innerProduct g g where g = ∑_S (if i∈S then f̂(S) else 0) * χ_S
  rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
      (∑ S, if i ∈ S then fourierCoeff f S * chiS S x else 0) ^ 2 =
      innerProduct (fun x => ∑ S, (if i ∈ S then fourierCoeff f S else 0) * chiS S x)
                   (fun x => ∑ S, (if i ∈ S then fourierCoeff f S else 0) * chiS S x) from by
    simp only [innerProduct, expect, uniformWeight, sq]
    congr 1
    apply Finset.sum_congr rfl; intro x _
    congr 1
    · apply Finset.sum_congr rfl; intro S _; by_cases hiS : i ∈ S <;> simp [hiS]
    · apply Finset.sum_congr rfl; intro S _; by_cases hiS : i ∈ S <;> simp [hiS]]
  -- Apply Parseval: innerProduct g g = ∑_S (f̂_g(S))^2
  rw [parseval]
  -- Compute: f̂_g(S) = if i∈S then f̂(S) else 0
  apply Finset.sum_congr rfl; intro S _
  have hfc : fourierCoeff (fun x => ∑ T, (if i ∈ T then fourierCoeff f T else 0) * chiS T x) S =
      if i ∈ S then fourierCoeff f S else 0 := by
    simp only [fourierCoeff, innerProduct, expect, uniformWeight]
    -- After unfolding, fourierCoeff f T = 2⁻ⁿ * ∑_y f(y) * χ_T(y), which appears in the goal
    -- Goal: 2⁻¹^n * ∑ y ∑ x (if i∈y then ...) * χ_y x * χ_S x = if i∈S then f̂(S) else 0
    -- Rearrange: swap x and T sums, then pull out 2⁻¹^n
    rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
        (∑ T, (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) * chiS T x) * chiS S x =
        ∑ T : Finset (Fin n), (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) *
          ((2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x) from by
      -- Rearrange: distribute 2⁻¹^n inside, expand T-sum, swap sums
      rw [show (2:ℝ)⁻¹^n * ∑ x : BoolCube n,
          (∑ T, (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) * chiS T x) * chiS S x =
          ∑ x : BoolCube n, ∑ T : Finset (Fin n),
            (if i ∈ T then 2⁻¹^n * ∑ y : BoolCube n, f y * chiS T y else 0) *
            ((2:ℝ)⁻¹^n * (chiS T x * chiS S x)) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro T _; ring]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro T _
      rw [← Finset.mul_sum, ← Finset.mul_sum]]
    simp_rw [show ∀ T : Finset (Fin n),
        (2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x = if T = S then 1 else 0 from fun T => by
      rw [show (2:ℝ)⁻¹^n * ∑ x, chiS T x * chiS S x =
          innerProduct (chiS T) (chiS S) from by simp [innerProduct, expect, uniformWeight]]
      exact fourier_coeff_chi T S]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hfc]
  by_cases hiS : i ∈ S <;> simp [hiS]
