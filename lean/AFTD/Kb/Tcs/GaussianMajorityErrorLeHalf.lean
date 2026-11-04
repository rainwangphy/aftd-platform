import AFTD.Prelude
import AFTD.Kb.Tcs.GaussianMajorityError

/-!
# gaussian_majority_error_le_half

Topic: communication   Node: 1ea520b758b2

Provenance: helper lemma. arXiv:2610.16830, target: gaussian_coin_majority_worst_variance_zeta_crossover

For any natural number q with 1 ≤ q and any real lam > 0, the error satisfies gaussian_majority_error q lam ≤ 1 / 2.
-/

lemma gaussian_majority_error_le_half_nonneg_of_ciInf {ι : Sort _} (F : ι → ℝ) (h : ∀ i, 0 ≤ F i) :
    0 ≤ ⨅ i, F i := by
  cases isEmpty_or_nonempty ι
  · simp
  · exact le_ciInf h

/-- The Gaussian majority communication error is bounded above by 1/2. -/
theorem gaussian_majority_error_le_half (q : ℕ) (hq : 1 ≤ q) (lam : ℝ) (hlam : 0 < lam) :
    gaussian_majority_error q lam ≤ 1 / 2 := by
  rw [gaussian_majority_error]
  refine ciInf_le_of_le ⟨0, ?_⟩ (fun _ : ℝ => (⟨0, hq⟩ : Fin q)) ?_
  · rintro _ ⟨f, rfl⟩
    apply gaussian_majority_error_le_half_nonneg_of_ciInf; intro hf
    apply gaussian_majority_error_le_half_nonneg_of_ciInf; intro g
    apply gaussian_majority_error_le_half_nonneg_of_ciInf; intro hg
    exact ENNReal.toReal_nonneg
  refine ciInf_le_of_le ⟨0, ?_⟩ measurable_const ?_
  · rintro _ ⟨hf, rfl⟩
    apply gaussian_majority_error_le_half_nonneg_of_ciInf; intro g
    apply gaussian_majority_error_le_half_nonneg_of_ciInf; intro hg
    exact ENNReal.toReal_nonneg
  refine ciInf_le_of_le ⟨0, ?_⟩ (fun _ _ => false) ?_
  · rintro _ ⟨g, rfl⟩
    apply gaussian_majority_error_le_half_nonneg_of_ciInf; intro hg
    exact ENNReal.toReal_nonneg
  refine ciInf_le_of_le ⟨0, ?_⟩ (fun _ => measurable_const) ?_
  · rintro _ ⟨hg, rfl⟩
    exact ENNReal.toReal_nonneg

  have h_set : {p : ℝ × ℝ | ((fun (_ _ : ℝ) => false) ((fun _ => (⟨0, hq⟩ : Fin q)) p.1) p.2 = true) ≠ (0 < p.1 + p.2)} =
      {p : ℝ × ℝ | 0 < p.1 + p.2} := by
    ext p
    dsimp
    simp
  rw [h_set]

  have hG1 : ProbabilityTheory.IsGaussian (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩) :=
    ProbabilityTheory.isGaussian_gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩
  have hP1 : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩) :=
    ProbabilityTheory.IsGaussian.toIsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩)
  have hG2 : ProbabilityTheory.IsGaussian (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.isGaussian_gaussianReal 0 1
  have hP2 : MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1) :=
    ProbabilityTheory.IsGaussian.toIsProbabilityMeasure (ProbabilityTheory.gaussianReal 0 1)
  have hSF1 : MeasureTheory.SFinite (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩) := inferInstance
  have hSF2 : MeasureTheory.SFinite (ProbabilityTheory.gaussianReal 0 1) := inferInstance

  set μ : MeasureTheory.Measure (ℝ × ℝ) :=
    (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩).prod (ProbabilityTheory.gaussianReal 0 1)
  have hPμ : MeasureTheory.IsProbabilityMeasure μ := inferInstance

  have h_symm_1 : MeasureTheory.Measure.map (fun x : ℝ => -x) (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩) =
      ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩ := by
    have h := @ProbabilityTheory.gaussianReal_map_neg 0 ⟨lam ^ 2, sq_nonneg lam⟩
    simp only [neg_zero] at h
    exact h
  have h_symm_2 : MeasureTheory.Measure.map (fun x : ℝ => -x) (ProbabilityTheory.gaussianReal 0 1) = ProbabilityTheory.gaussianReal 0 1 := by
    have h := @ProbabilityTheory.gaussianReal_map_neg 0 1
    simp only [neg_zero] at h
    exact h
  have h_symm : MeasureTheory.Measure.map (fun p : ℝ × ℝ => (-p.1, -p.2)) μ = μ := by
    have h := (MeasureTheory.Measure.map_prod_map (ProbabilityTheory.gaussianReal 0 ⟨lam ^ 2, sq_nonneg lam⟩)
      (ProbabilityTheory.gaussianReal 0 1) measurable_neg measurable_neg).symm
    rw [h_symm_1, h_symm_2] at h
    exact h

  set S : Set (ℝ × ℝ) := {p | 0 < p.1 + p.2}
  set neg_map : ℝ × ℝ → ℝ × ℝ := fun p => (-p.1, -p.2)
  have hS_meas : MeasurableSet S :=
    measurableSet_Ioi.preimage (measurable_fst.add measurable_snd)
  have h_neg_meas : Measurable neg_map := measurable_neg
  have h_map_S : μ (neg_map ⁻¹' S) = μ S := by
    have := (MeasureTheory.Measure.map_apply (μ := μ) h_neg_meas hS_meas).symm
    rw [h_symm] at this
    exact this
  have h_disj : Disjoint S (neg_map ⁻¹' S) := by
    rw [Set.disjoint_iff]
    rintro p ⟨hp1, hp2⟩
    dsimp [S, neg_map] at hp1 hp2
    linarith
  have h_union : S ∪ (neg_map ⁻¹' S) ⊆ Set.univ := Set.subset_univ _
  have h_meas_union : μ (S ∪ (neg_map ⁻¹' S)) = μ S + μ (neg_map ⁻¹' S) :=
    MeasureTheory.measure_union h_disj (hS_meas.preimage h_neg_meas)
  rw [h_map_S] at h_meas_union
  have h_le_univ : μ (S ∪ (neg_map ⁻¹' S)) ≤ μ Set.univ := MeasureTheory.measure_mono h_union
  rw [MeasureTheory.measure_univ (μ := μ)] at h_le_univ
  rw [h_meas_union] at h_le_univ
  have h2 : 2 * μ S = μ S + μ S := two_mul (μ S)
  rw [← h2] at h_le_univ
  have h_mu_le_half : μ S ≤ 1 / 2 :=
    ENNReal.le_div_iff_mul_le (Or.inr (by simp)) (Or.inr (by simp)) |>.2 (by simpa [mul_comm] using h_le_univ)
  have h_half : ((1 : ℝ) / 2) = ENNReal.toReal (1 / 2) := by simp
  rw [h_half]
  exact ENNReal.toReal_mono (by norm_num) h_mu_le_half
