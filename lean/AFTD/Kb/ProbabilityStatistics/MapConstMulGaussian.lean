import AFTD.Prelude

/-!
# map_const_mul_gaussian

Topic: concentration   Node: e1f76c47cd69

Provenance: helper lemma. TCSlib, `map_const_mul_gaussian`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Scaling a centered real Gaussian. Let $X\colon \Omega \to \bbr$ be a measurable random variable on a measure space
$(\Omega, \mu)$ whose law is the centered Gaussian $N(0, \sigma_0)$ with variance
$\sigma_0 \ge 0$. Then for every scalar $c \in \bbr$, the scaled variable $c\,X$ has law
\[
  N\!\bigl(0,\; c^2 \sigma_0\bigr),
\]
the centered Gaussian with variance $c^2 \sigma_0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- If a measurable real random variable `X` has law `N(0, σ₀)` (Mathlib's `gaussianReal` with variance parameter `σ₀`), then for any real `c` the scalar multiple `c·X` has law `N(0, c²·σ₀)`. This is the scaling step of [DG03, §2] (a linear image of a centered Gaussian is a centered Gaussian); it is an auxiliary restatement of Mathlib's `gaussianReal_map_const_mul` that is easier to apply. -/
lemma map_const_mul_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {σ₀ : NNReal}
    (hX_meas : Measurable X)
    (hX : Measure.map X μ = gaussianReal 0 σ₀)
    (c : ℝ) :
    Measure.map (fun ω => c * X ω) μ =
      gaussianReal 0 (⟨c ^ 2, sq_nonneg _⟩ * σ₀) := by
  have : (fun ω => c * X ω) = (fun r : ℝ => c * r) ∘ X := rfl
  rw [this, ← Measure.map_map (by fun_prop) hX_meas, hX,
    gaussianReal_map_const_mul]
  simp only [mul_zero]
  rfl
