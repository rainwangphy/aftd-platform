import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.ChiSquaredTail
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.ConcentrationZero
import AFTD.Kb.ProbabilityStatistics.MapConstMulGaussian
import AFTD.Kb.ProbabilityStatistics.NormSqToEuclideanLin
import AFTD.Kb.ProbabilityStatistics.RowsIndep
import AFTD.Kb.ProbabilityStatistics.SumScaledIidGaussianMap
import AFTD.Kb.ProbabilityStatistics.ToEuclideanLinApplyEqSum
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib

/-!
# jl_concentration_single_via_chi_squared

Topic: concentration   Node: cea0fe325257

Provenance: helper lemma. TCSlib, `jl_concentration_single_via_chi_squared`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ConcentrationBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Johnson–Lindenstrauss concentration for a single vector. Let $k \ge 1$, and let $A$ be a random $k \times d$ real matrix on a probability space
$(\Omega, \mu)$ whose $kd$ entries $A_{ij}$ are jointly independent, each Gaussian with
law $N(0, 1/k)$. Then for every fixed vector $x \in \bbr^d$ and every $\varepsilon$ with
$0 < \varepsilon < 1$,
\[
\mu\bigl\{\,\omega : \bigl|\,\|A(\omega)\,x\|^2 - \|x\|^2\,\bigr| > \varepsilon\,\|x\|^2
\,\bigr\}
  \;\le\; 2\exp\!\Bigl(-\frac{k\,\varepsilon^2}{8}\Bigr),
\]
where $\|A(\omega)\,x\|$ denotes the Euclidean norm of the image $A(\omega)\,x \in
\bbr^k$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Single-vector JL concentration for iid Gaussian matrices.** Let `A` be a random `k × d` matrix (`k > 0`) whose entries are iid `N(0, 1/k)` — formally: `A` is measurable, each entry has law `N(0, 1/k)`, the entries within each row are mutually independent, and the rows are mutually independent. Then for every fixed vector `x` and every `0 < ε < 1`, `ℙ[ ε‖x‖² < |‖Ax‖² − ‖x‖²| ] ≤ 2·exp(−kε²/8)`. This is [DG03, Lemma 2.2] (with the two-sided bound noted at `chi_squared_tail`) and the analogue of [Ver18, Lemma 5.3.2]. Deviation: the sources treat a random orthogonal projection (and [Ver18] an unspecified constant `c`); here the iid-Gaussian-matrix variant with the explicit two-sided constant `2·exp(−kε²/8)`, cf. [Ver18, §5.3]. **Proof sketch.** If `x = 0` the bad event is empty (`concentration_zero`). Otherwise `‖x‖ > 0` and: Step 1: set `Y i = (Ax)_i = ∑ j, A i j · x j`; by `sum_scaled_iid_gaussian_map` applied to the `i`-th row, each `Y i` has law `N(0, ‖x‖²/k)`. Step 2: by `rows_indep` the `Y i` are mutually independent. Step 3: set `Z i = Y i / ‖x‖`; by `map_const_mul_gaussian` each `Z i` has law `N(0, 1/k)`, and independence is preserved. Step 4: `‖Ax‖² = ∑ i, (Y i)² = ‖x‖² · ∑ i, (Z i)²` (`norm_sq_toEuclideanLin`). Step 5: hence the bad event `ε‖x‖² < |‖Ax‖² − ‖x‖²|` is the event `ε < |∑ i, (Z i)² − 1|`, dividing by `‖x‖² > 0`. Step 6: apply the chi-squared tail bound `chi_squared_tail` to `Z`. -/
theorem jl_concentration_single_via_chi_squared (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (hA_law : ∀ (i : Fin k) (j : Fin d),
      Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hRowEntryIndep : ∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (x : EuclideanSpace ℝ (Fin d))
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    (μ {ω | BadSingle ε (A ω) x}).toReal ≤
      2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
  by_cases hx : x = 0
  · subst hx
    exact concentration_zero μ A ε
  -- Otherwise ‖x‖ > 0; the numbered steps below follow the proof sketch in the
  -- docstring.
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_norm_sq_pos : 0 < ‖x‖ ^ 2 := by positivity
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
  -- Helper: ‖x‖² = ∑ j, (x j)²
  have hxnorm_sq : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [sq_abs]
  -- Step 1: define `Y i := (A·).toEuclideanLin x i` and establish its
  -- distribution.
  set Y : Fin k → Ω → ℝ :=
    fun i ω => (A ω).toEuclideanLin x i with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    have heq : Y i = fun ω => ∑ j, (A ω) i j * x j := by
      funext ω
      change (A ω).toEuclideanLin x i = ∑ j, (A ω) i j * x j
      rfl
    rw [heq]
    exact Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA_meas)).mul_const _)
  -- Each `Y i` has distribution `N(0, ‖x‖²/k)`.
  have hY_law : ∀ i, Measure.map (Y i) μ =
      gaussianReal 0 ⟨‖x‖ ^ 2 / k, by positivity⟩ := by
    intro i
    -- Apply `sum_scaled_iid_gaussian_map` to the i-th row.
    have hrow_law : ∀ j, Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩ := fun j => hA_law i j
    have hrow_meas : ∀ j, Measurable (fun ω => A ω i j) := fun j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA_meas)
    have hrow_indep : iIndepFun (fun (j : Fin d) ω => A ω i j) μ := hRowEntryIndep i
    have hY_eq : Y i = fun ω => ∑ j, x j * (A ω i j) := by
      funext ω
      change (A ω).toEuclideanLin x i = _
      rw [toEuclideanLin_apply_eq_sum]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [hY_eq]
    have := sum_scaled_iid_gaussian_map (Y := fun j ω => A ω i j)
      hrow_meas hrow_law hrow_indep x Finset.univ
    rw [this]
    -- Match the variance: ⟨∑j, (x j)², _⟩ * ⟨1/k, _⟩ = ⟨‖x‖²/k, _⟩
    congr 1
    apply NNReal.eq
    show (∑ j, x j ^ 2) * (1 / (k : ℝ)) = ‖x‖ ^ 2 / k
    rw [← hxnorm_sq]
    ring
  -- Step 2: rows are independent as scalar projections.
  have hY_indep : iIndepFun Y μ := rows_indep A hRowsIndep x
  -- Step 3: Define `Z i := (1/‖x‖) · Y i`. Each `Z i ~ N(0, 1/k)`.
  set Z : Fin k → Ω → ℝ := fun i ω => (1 / ‖x‖) * Y i ω with hZ_def
  have hZ_meas : ∀ i, Measurable (Z i) := fun i => (hY_meas i).const_mul _
  have hZ_law : ∀ i, Measure.map (Z i) μ =
      gaussianReal 0 ⟨1 / k, by positivity⟩ := by
    intro i
    have := map_const_mul_gaussian (hY_meas i) (hY_law i) (1 / ‖x‖)
    rw [this]
    congr 1
    apply NNReal.eq
    show (1 / ‖x‖) ^ 2 * (‖x‖ ^ 2 / k) = 1 / (k : ℝ)
    field_simp
  have hZ_indep : iIndepFun Z μ :=
    hY_indep.comp (fun _ r => (1 / ‖x‖) * r)
      (fun _ => measurable_const.mul measurable_id)
  -- Step 4: `∑ i, (Y i)² = ‖x‖² · ∑ i, (Z i)²`.
  have hY_eq_xZ : ∀ i ω, Y i ω = ‖x‖ * Z i ω := by
    intro i ω
    simp only [Z]
    field_simp
  have hsum_sq : ∀ ω, ∑ i, (Y i ω) ^ 2 = ‖x‖ ^ 2 * ∑ i, (Z i ω) ^ 2 := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hY_eq_xZ i ω]
    ring
  -- Step 5: the bad event matches `{ω | ε < |∑ i, (Z i ω)² - 1|}`.
  have hbad_eq : {ω | BadSingle ε (A ω) x} = {ω | ε < |(∑ i, (Z i ω) ^ 2) - 1|} := by
    ext ω
    simp only [BadSingle, Set.mem_setOf_eq]
    rw [norm_sq_toEuclideanLin]
    show ε * ‖x‖ ^ 2 < _ ↔ _
    rw [show (∑ i, ((A ω).toEuclideanLin x i) ^ 2) = ∑ i, (Y i ω) ^ 2 from rfl,
        hsum_sq]
    rw [show ‖x‖ ^ 2 * (∑ i, (Z i ω) ^ 2) - ‖x‖ ^ 2 =
            ‖x‖ ^ 2 * ((∑ i, (Z i ω) ^ 2) - 1) from by ring]
    rw [abs_mul, abs_of_pos hx_norm_sq_pos]
    constructor
    · intro h; nlinarith [hx_norm_sq_pos, h]
    · intro h; nlinarith [hx_norm_sq_pos, h, abs_nonneg ((∑ i, (Z i ω) ^ 2) - 1)]
  rw [hbad_eq]
  -- Step 6: Apply `chi_squared_tail`.
  exact chi_squared_tail μ hk_pos Z hZ_meas hZ_law hZ_indep ε hε_pos hε_lt
