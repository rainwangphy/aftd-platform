import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluence
import AFTD.Kb.Tcs.BooleanAnalysisTotalInfluenceEqSumSqDeg
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.KKLIsJunta
import AFTD.Kb.Tcs.KKLInfluentialCoords
import AFTD.Kb.Tcs.KKLInfluentialCoordsCard
import AFTD.Kb.Tcs.KKLL2DistSq
import AFTD.Kb.Tcs.KKLLowDegreePart
import AFTD.Kb.Tcs.KKLLowDegreePartDependsOnInfluential
import AFTD.Kb.Tcs.KKLLowDegreeApprox
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.G

/-!
# KKL.friedgut_junta

Topic: combinatorics   Node: 2c5f7ed630d1

Provenance: formalization of a published result. Source: Friedgut's junta theorem, as formalized in TCSlib (`KKL.friedgut_junta`). Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Friedgut's junta theorem. Let $f : \{0,1\}^n \to \{-1,1\}$ be a $\pm 1$-valued Boolean function with total
influence $I[f]$, and let $\varepsilon > 0$. Then there exist a coordinate set $J
\subseteq [n]$ and a Boolean function $g : \{0,1\}^n \to \bbr$ such that
\[
  \abs{J} \;\le\; \frac{4n\,I[f]}{\varepsilon},
\]
$g$ is a $J$-junta, and $\E\big[(f(x) - g(x))^2\big] \le \varepsilon$ under the uniform
measure on the cube.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
/-- **Friedgut's Junta Theorem** (1998): Any Boolean function `f : {-1,1}^n -> {-1,1}` is `epsilon`-close (in L2) to a function that depends on at most `ceil(4 * n * I[f] / epsilon)` coordinates. Proof strategy: 1. Set `k = ceil(4 * I[f] / epsilon)` and `tau = epsilon / (4 * n)`. 2. The low-degree part `f_{<=k}` satisfies `E[(f - f_{<=k})^2] <= I[f]/k <= epsilon/4`. 3. There are at most `I[f] / tau = 4 * n * I[f] / epsilon` coordinates with `Inf_i >= tau`. 4. Restricting to those coordinates loses at most `n * tau = epsilon/4` in L2 from `f_{<=k}`. 5. By the triangle inequality: `l2DistSq f g <= 2 * (epsilon/4 + epsilon/4) = epsilon`. **Source:** [OD14, Ch. 10]. **Deviation:** The stated junta-size bound is a deliberately weaker finite-dimensional form than the standard asymptotic theorem. -/
theorem KKL.friedgut_junta (f : BooleanFunc n) (hf : isPmOne f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (J : Finset (Fin n)) (g : BooleanFunc n),
      (J.card : ℝ) ≤ 4 * n * totalInfluence f / ε ∧
      IsJunta g J ∧
      l2DistSq f g ≤ ε := by
  -- Step A: Choose the degree truncation level
  have hk : 0 < ⌈totalInfluence f / (ε / 2)⌉₊ ∨ totalInfluence f ≤ 0 := by
    by_cases hI : totalInfluence f ≤ 0
    · right; exact hI
    · left
      push_neg at hI
      apply Nat.ceil_pos.mpr
      apply div_pos hI
      linarith
  -- Step B: Low-degree approximation
  have hlow : ∀ (k : ℕ), 0 < k →
      l2DistSq f (lowDegreePart f k) ≤ totalInfluence f / k := by
    intro k hk
    exact lowDegree_approx f k hk
  -- Step C: Junta approximation of lowDegreePart
  -- The lowDegreePart depends on coordinates appearing in its Fourier support.
  -- We approximate it by a junta on influential coordinates.
  have hjunta : ∀ (k : ℕ) (τ : ℝ), 0 < τ →
      ∃ (J : Finset (Fin n)) (g : BooleanFunc n),
        (J.card : ℝ) ≤ totalInfluence f / τ ∧
        IsJunta g J ∧
        l2DistSq (lowDegreePart f k) g ≤ (n : ℝ) * τ := by
    intro k τ hτ
    obtain ⟨g, hg_junta, hg_err⟩ := lowDegreePart_depends_on_influential f k τ hτ
    exact ⟨influentialCoords f τ, g, influential_coords_card f τ hτ, hg_junta, hg_err⟩
  -- Step D: Triangle inequality for L2 and parameter optimization
  -- Triangle inequality: l2DistSq f g ≤ 2*(l2DistSq f h + l2DistSq h g)
  -- (follows from (a-c)^2 ≤ 2*(a-b)^2 + 2*(b-c)^2 pointwise)
  have htri : ∀ (p q r : BooleanFunc n),
      l2DistSq p r ≤ 2 * l2DistSq p q + 2 * l2DistSq q r := by
    intro p q r
    simp only [l2DistSq, expect, uniformWeight]
    have hw : (0 : ℝ) ≤ 2⁻¹ ^ n := by positivity
    calc 2⁻¹ ^ n * ∑ x : BoolCube n, (p x - r x) ^ 2
        ≤ 2⁻¹ ^ n * (2 * ∑ x : BoolCube n, (p x - q x) ^ 2 +
                      2 * ∑ x : BoolCube n, (q x - r x) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hw
          have hrw : 2 * ∑ x : BoolCube n, (p x - q x) ^ 2 +
                     2 * ∑ x : BoolCube n, (q x - r x) ^ 2 =
              ∑ x : BoolCube n, (2 * (p x - q x) ^ 2 + 2 * (q x - r x) ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          rw [hrw]
          apply Finset.sum_le_sum; intro x _
          nlinarith [sq_nonneg (p x - q x - (q x - r x))]
      _ = 2 * (2⁻¹ ^ n * ∑ x, (p x - q x) ^ 2) +
          2 * (2⁻¹ ^ n * ∑ x, (q x - r x) ^ 2) := by ring
  -- Handle the I[f] = 0 case first
  by_cases hI : totalInfluence f ≤ 0
  · -- I[f] = 0 (since totalInfluence is a sum of nonneg terms)
    have hI0 : totalInfluence f = 0 := le_antisymm hI (by
      rw [totalInfluence_eq_sum_sq_deg]
      apply Finset.sum_nonneg; intro S _; positivity)
    -- Sub-case: n = 0
    by_cases hn : n = 0
    · -- BoolCube 0 is a singleton; f is trivially constant
      refine ⟨∅, f, ?_, ?_, ?_⟩
      · simp [hn]
      · intro x y _
        -- Fin 0 → Bool has a unique element (empty domain)
        subst hn
        exact congrArg f (Subsingleton.elim x y)
      · simp only [l2DistSq]
        have hzero : (fun x : BoolCube n => (f x - f x) ^ 2) = fun _ => (0 : ℝ) := by
          ext x; ring
        rw [hzero]
        simp [expect, uniformWeight, Finset.sum_const_zero]
        linarith
    · -- n > 0, I = 0: use k = 1 and τ = ε/(2*n)
      have hn' : 0 < n := Nat.pos_of_ne_zero hn
      set τ₀ := ε / (2 * (↑n : ℝ)) with hτ₀_def
      have hτ₀ : 0 < τ₀ := by positivity
      have hτ₀n : (↑n : ℝ) * τ₀ = ε / 2 := by
        have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn'
        simp only [hτ₀_def]
        field_simp [hn_pos.ne', hε.ne']
      obtain ⟨J, g, hJcard, hJjunta, hJerr⟩ := hjunta 1 τ₀ hτ₀
      refine ⟨J, g, ?_, hJjunta, ?_⟩
      · -- |J| ≤ I/τ₀ = 0 ≤ 4*n*0/ε
        calc (J.card : ℝ) ≤ totalInfluence f / τ₀ := hJcard
          _ = 0 := by rw [hI0]; simp
          _ ≤ 4 * ↑n * totalInfluence f / ε := by rw [hI0]; simp
      · -- l2DistSq f g ≤ ε
        -- hlow 1: l2DistSq f (lowDeg 1) ≤ I/1 = 0
        -- hJerr: l2DistSq (lowDeg 1) g ≤ n * τ₀ = ε/2
        -- triangle: l2DistSq f g ≤ 2*(0 + ε/2) = ε
        have hlow1 := hlow 1 (by norm_num)
        have hlow_zero : l2DistSq f (lowDegreePart f 1) ≤ 0 := by
          calc l2DistSq f (lowDegreePart f 1) ≤ totalInfluence f / ↑(1 : ℕ) := hlow1
            _ = 0 := by simp [hI0]
        have hjerr_half : l2DistSq (lowDegreePart f 1) g ≤ ε / 2 := by
          calc l2DistSq (lowDegreePart f 1) g ≤ ↑n * τ₀ := hJerr
            _ = ε / 2 := hτ₀n
        have hd_nn : 0 ≤ l2DistSq f (lowDegreePart f 1) := by
          simp only [l2DistSq, expect, uniformWeight]
          apply mul_nonneg (by positivity)
          apply Finset.sum_nonneg; intro x _; positivity
        calc l2DistSq f g
            ≤ 2 * l2DistSq f (lowDegreePart f 1) + 2 * l2DistSq (lowDegreePart f 1) g :=
              htri f (lowDegreePart f 1) g
          _ ≤ 2 * 0 + 2 * (ε / 2) := by linarith
          _ = ε := by ring
  · -- I[f] > 0
    push_neg at hI
    -- Derive n > 0 from I[f] > 0
    have hn : 0 < n := by
      by_contra h0; push_neg at h0
      have h_n0 : n = 0 := Nat.le_zero.mp h0
      subst h_n0
      simp [totalInfluence] at hI
    -- Choose parameters: τ = ε/(4*n), k = ⌈4*I/ε⌉₊
    set τ := ε / (4 * ↑n) with hτ_def
    have hτ : 0 < τ := by positivity
    have hτn : (↑n : ℝ) * τ = ε / 4 := by
      have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
      simp only [hτ_def]
      field_simp [hn_pos.ne', hε.ne']
    set k := ⌈4 * totalInfluence f / ε⌉₊ with hk_def
    have hk_pos : 0 < k := Nat.ceil_pos.mpr (by positivity)
    -- Get junta from hjunta
    have hlow_k := hlow k hk_pos
    obtain ⟨J, g, hJcard, hJjunta, hJerr⟩ := hjunta k τ hτ
    refine ⟨J, g, ?_, hJjunta, ?_⟩
    -- Junta size bound: |J| ≤ I/τ = 4*n*I/ε
    · calc (J.card : ℝ)
          ≤ totalInfluence f / τ := hJcard
        _ = 4 * ↑n * totalInfluence f / ε := by
            have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
            simp only [hτ_def]
            field_simp [hn_pos.ne', hε.ne']
    -- L2 error bound: l2DistSq f g ≤ ε
    · -- Low-degree error: I/k ≤ ε/4
      have hlow_bound : l2DistSq f (lowDegreePart f k) ≤ ε / 4 := by
        apply le_trans hlow_k
        rw [div_le_div_iff₀ (Nat.cast_pos.mpr hk_pos) (by norm_num : (0:ℝ) < 4)]
        -- Goal: totalInfluence f * 4 ≤ ε * ↑k
        have hle : 4 * totalInfluence f / ε ≤ (k : ℝ) := Nat.le_ceil _
        have h := (div_le_iff₀ hε).mp hle
        linarith
      -- Junta error: n*τ = ε/4
      have hjunta_bound : l2DistSq (lowDegreePart f k) g ≤ ε / 4 := by
        calc l2DistSq (lowDegreePart f k) g ≤ (↑n) * τ := hJerr
          _ = ε / 4 := hτn
      -- Triangle inequality gives total error ≤ 2*(ε/4 + ε/4) = ε
      calc l2DistSq f g
          ≤ 2 * l2DistSq f (lowDegreePart f k) + 2 * l2DistSq (lowDegreePart f k) g :=
            htri f (lowDegreePart f k) g
        _ ≤ 2 * (ε / 4) + 2 * (ε / 4) := by linarith
        _ = ε := by ring
