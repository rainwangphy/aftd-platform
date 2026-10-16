import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.MapConstMulGaussian

/-!
# sum_scaled_iid_gaussian_map

Topic: concentration   Node: 3a968d16953a

Provenance: helper lemma. TCSlib, `sum_scaled_iid_gaussian_map`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Weighted sum of independent Gaussians is Gaussian. Let $(\Omega,\mu)$ be a probability space, and let $(Y_j)_{j}$ be a family of
independent, measurable real-valued random variables, each distributed as a centred
Gaussian with mean $0$ and variance $\sigma_0 \ge 0$. Then for any real coefficients
$(x_j)_j$ and any finite index set $s$, the random variable $\sum_{j \in s} x_j\, Y_j$
has distribution $N\!\Bigl(0,\; \bigl(\sum_{j \in s} x_j^2\bigr)\,\sigma_0\Bigr)$; that
is, its law is the centred Gaussian on $\bbr$ with variance $\sigma_0 \sum_{j \in s}
x_j^2$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Row-projection is Gaussian.** If `Y j` are mutually independent measurable real random variables each with law `N(0, σ₀)` and `x j : ℝ` are fixed coefficients, then for every finite set `s` of indices the weighted sum `∑ j ∈ s, x j · Y j` has law `N(0, (∑ j ∈ s, (x j)²) · σ₀)` under `μ`. This is the observation of [DG03, §2] that the projection of iid Gaussians is Gaussian with variance `‖x‖²/k` (DG03 work with a random orthogonal projection; the iid-Gaussian-matrix form used here is the standard variant, cf. [Ver18, §5.3]). **Proof sketch.** Step 1: the scaled family `Z j = x j · Y j` is measurable, each `Z j` has law `N(0, (x j)²·σ₀)` by `map_const_mul_gaussian`, and the `Z j` are mutually independent as images of the `Y j`. Step 2: induct on the finite set `s`. In the empty case the sum is identically `0`, whose law is the Dirac mass at `0`, i.e. `N(0, 0)`. Step 3 (insert case): split the sum as `Z j₀` plus the sum over the remaining indices; the two are independent (Mathlib's `iIndepFun.indepFun_finset_sum_of_notMem`), the partial sum is Gaussian by the induction hypothesis, and the sum of two independent centered Gaussians is centered Gaussian with added variances (`gaussianReal_add_gaussianReal_of_indepFun`); finally match the variance expression. -/
lemma sum_scaled_iid_gaussian_map
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {σ₀ : NNReal}
    (hY_meas : ∀ j, Measurable (Y j))
    (hY_law : ∀ j, Measure.map (Y j) μ = gaussianReal 0 σ₀)
    (hY_indep : iIndepFun Y μ)
    (x : ι → ℝ) (s : Finset ι) :
    Measure.map (fun ω => ∑ j ∈ s, x j * Y j ω) μ =
      gaussianReal 0
        (⟨∑ j ∈ s, (x j) ^ 2,
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩ * σ₀) := by
  classical
  -- Step 1: the family `Z j := x j * Y j` is independent Gaussian by `iIndepFun.comp`.
  set Z : ι → Ω → ℝ := fun j ω => x j * Y j ω with hZ_def
  have hZ_meas : ∀ j, Measurable (Z j) := fun j => (hY_meas j).const_mul (x j)
  have hZ_law : ∀ j, Measure.map (Z j) μ =
      gaussianReal 0 (⟨(x j) ^ 2, sq_nonneg _⟩ * σ₀) := fun j =>
    map_const_mul_gaussian (hY_meas j) (hY_law j) (x j)
  have hZ_indep : iIndepFun Z μ :=
    hY_indep.comp (fun j r => x j * r) (fun j => measurable_const.mul measurable_id)
  -- Step 2: induction on `s`.
  induction s using Finset.induction_on with
  | empty =>
    -- The sum is constantly 0, so its law is `Dirac 0 = gaussianReal 0 0`.
    have hLHS : (fun ω => ∑ j ∈ (∅ : Finset ι), x j * Y j ω) = (fun _ => (0 : ℝ)) := by
      funext ω; simp
    rw [hLHS, Measure.map_const, measure_univ, one_smul,
        ← gaussianReal_zero_var (0 : ℝ), gaussianReal_ext_iff]
    refine ⟨rfl, ?_⟩
    apply NNReal.eq
    show (0 : ℝ) = 0 * (σ₀ : ℝ)
    ring
  | insert j₀ s' hj₀ ih =>
    -- Step 3: split the sum and use independence + Gaussian add.
    have hsplit : (fun ω => ∑ j ∈ insert j₀ s', x j * Y j ω) =
        (Z j₀ + ∑ j ∈ s', Z j) := by
      funext ω
      change ∑ j ∈ insert j₀ s', x j * Y j ω = Z j₀ ω + (∑ j ∈ s', Z j) ω
      rw [Finset.sum_insert hj₀, Finset.sum_apply]
    rw [hsplit]
    -- Independence between `Z j₀` and the partial sum over `s'`.
    have hindep : IndepFun (Z j₀) (∑ j ∈ s', Z j) μ :=
      (hZ_indep.indepFun_finset_sum_of_notMem hZ_meas hj₀).symm
    -- Law of the partial sum: massage the IH from the `fun ω => ...` form to the
    -- Pi-sum form `∑ j ∈ s', Z j`.
    have hpartial_eq : (fun ω => ∑ j ∈ s', x j * Y j ω) = ∑ j ∈ s', Z j := by
      funext ω
      change _ = (∑ j ∈ s', Z j) ω
      rw [Finset.sum_apply]
    rw [hpartial_eq] at ih
    -- Combine using `gaussianReal_add_gaussianReal_of_indepFun`.
    rw [gaussianReal_add_gaussianReal_of_indepFun hindep (hZ_law j₀) ih]
    -- Match the variance form. Use `gaussianReal_ext_iff` to split into mean + variance.
    rw [gaussianReal_ext_iff]
    refine ⟨by ring, ?_⟩
    apply NNReal.eq
    show x j₀ ^ 2 * (σ₀ : ℝ) + (∑ j ∈ s', x j ^ 2) * σ₀ = (∑ j ∈ insert j₀ s', x j ^ 2) * σ₀
    rw [Finset.sum_insert hj₀]
    ring
