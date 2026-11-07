import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCriticalOverlapIntegral
import AFTD.Kb.Physics.EnergyFilterCriticalGaussianKernel
import AFTD.Kb.Physics.EnergyFilterCriticalWindowIntegral

/-!
# energy_filter_critical_overlap_integral_pos

Topic: statistical_mechanics   Node: 792842bf2eac

Provenance: original. Related work: arXiv:2405.02158, Energy-filtered quantum states and the emergence of non-local correlations

For any c > 0, the critical overlap integral energy_filter_critical_overlap_integral c is strictly positive.
-/

open MeasureTheory

lemma energy_filter_critical_overlap_integral_pos_kernel_pos (x : ℝ) :
    0 < energy_filter_critical_gaussian_kernel x := by
  unfold energy_filter_critical_gaussian_kernel
  positivity

lemma energy_filter_critical_overlap_integral_pos_kernel_continuous :
    Continuous energy_filter_critical_gaussian_kernel := by
  unfold energy_filter_critical_gaussian_kernel
  continuity

lemma energy_filter_critical_overlap_integral_pos_kernel_integrable :
    Integrable energy_filter_critical_gaussian_kernel := by
  unfold energy_filter_critical_gaussian_kernel
  have h1 : Integrable (fun x : ℝ => Real.exp (-4 * x^2)) := by
    have h : (0 : ℝ) < 4 := by norm_num
    exact integrable_exp_neg_mul_sq h
  have h2 : Integrable (fun x : ℝ => (2 / Real.sqrt Real.pi) * Real.exp (-4 * x^2)) :=
    h1.const_mul _
  have heq : (fun x : ℝ => 2 * Real.exp (-4 * x^2) / Real.sqrt Real.pi) =
             (fun x : ℝ => (2 / Real.sqrt Real.pi) * Real.exp (-4 * x^2)) := by
    ext x
    ring
  rw [heq]
  exact h2

lemma energy_filter_critical_overlap_integral_pos_window_integral_pos (c x : ℝ) (hc : 0 < c) :
    0 < energy_filter_critical_window_integral c x := by
  unfold energy_filter_critical_window_integral
  have hab : -c - x < -x := by linarith
  apply intervalIntegral.integral_pos hab energy_filter_critical_overlap_integral_pos_kernel_continuous.continuousOn
  · intro y _
    exact (energy_filter_critical_overlap_integral_pos_kernel_pos y).le
  · exact ⟨-x, by constructor <;> linarith, energy_filter_critical_overlap_integral_pos_kernel_pos (-x)⟩

lemma energy_filter_critical_overlap_integral_pos_window_integral_continuous (c : ℝ) :
    Continuous (energy_filter_critical_window_integral c) := by
  have h_int : ∀ a b, IntervalIntegrable energy_filter_critical_gaussian_kernel volume a b :=
    fun a b => energy_filter_critical_overlap_integral_pos_kernel_continuous.intervalIntegrable a b
  have h_prim : Continuous (fun u => ∫ y in (0 : ℝ)..u, energy_filter_critical_gaussian_kernel y) :=
    intervalIntegral.continuous_primitive h_int 0
  have h_eq : energy_filter_critical_window_integral c =
      (fun x => (∫ y in (0 : ℝ)..(-x), energy_filter_critical_gaussian_kernel y) -
                (∫ y in (0 : ℝ)..(-c - x), energy_filter_critical_gaussian_kernel y)) := by
    ext x
    unfold energy_filter_critical_window_integral
    rw [← intervalIntegral.integral_interval_sub_left (h_int 0 (-x)) (h_int 0 (-c - x))]
  rw [h_eq]
  exact (h_prim.comp continuous_neg).sub (h_prim.comp (continuous_const.sub continuous_id))

lemma energy_filter_critical_overlap_integral_pos_kernel_le_const (y : ℝ) :
    energy_filter_critical_gaussian_kernel y ≤ 2 / Real.sqrt Real.pi := by
  unfold energy_filter_critical_gaussian_kernel
  have hpi : 0 < Real.sqrt Real.pi := by positivity
  have hexp : Real.exp (-4 * y^2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp_of_le
    nlinarith
  have hmul : 2 * Real.exp (-4 * y^2) ≤ 2 := by linarith
  exact div_le_div_of_nonneg_right hmul hpi.le

lemma energy_filter_critical_overlap_integral_pos_window_integral_le_const (c x : ℝ) (hc : 0 < c) :
    energy_filter_critical_window_integral c x ≤ c * (2 / Real.sqrt Real.pi) := by
  unfold energy_filter_critical_window_integral
  have hab : -c - x ≤ -x := by linarith
  have h_int_const : IntervalIntegrable (fun _ => 2 / Real.sqrt Real.pi) volume (-c - x) (-x) :=
    intervalIntegrable_const
  have h_int_k : IntervalIntegrable energy_filter_critical_gaussian_kernel volume (-c - x) (-x) :=
    energy_filter_critical_overlap_integral_pos_kernel_continuous.intervalIntegrable _ _
  have h_mono := intervalIntegral.integral_mono_on hab h_int_k h_int_const (fun y _ => energy_filter_critical_overlap_integral_pos_kernel_le_const y)
  have h_eval : ∫ (u : ℝ) in (-c - x)..(-x), (2 / Real.sqrt Real.pi) = c * (2 / Real.sqrt Real.pi) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring_nf
  rwa [h_eval] at h_mono

/-- The critical overlap integral D_c is strictly positive for any c > 0. -/
theorem energy_filter_critical_overlap_integral_pos (c : ℝ) (hc : 0 < c) :
    0 < energy_filter_critical_overlap_integral c := by
  unfold energy_filter_critical_overlap_integral
  let f : ℝ → ℝ := fun x => energy_filter_critical_gaussian_kernel x * energy_filter_critical_window_integral c x
  have hfc : Continuous f :=
    energy_filter_critical_overlap_integral_pos_kernel_continuous.mul
      (energy_filter_critical_overlap_integral_pos_window_integral_continuous c)
  have hf_le : ∀ x, ‖f x‖ ≤ (c * (2 / Real.sqrt Real.pi)) * energy_filter_critical_gaussian_kernel x := by
    intro x
    dsimp [f]
    rw [abs_of_pos (mul_pos (energy_filter_critical_overlap_integral_pos_kernel_pos x)
      (energy_filter_critical_overlap_integral_pos_window_integral_pos c x hc))]
    have := energy_filter_critical_overlap_integral_pos_window_integral_le_const c x hc
    have hk := (energy_filter_critical_overlap_integral_pos_kernel_pos x).le
    nlinarith
  have hg_int : MeasureTheory.Integrable (fun x => (c * (2 / Real.sqrt Real.pi)) * energy_filter_critical_gaussian_kernel x) :=
    energy_filter_critical_overlap_integral_pos_kernel_integrable.const_mul _
  have hfi : MeasureTheory.Integrable f :=
    hg_int.mono' hfc.aestronglyMeasurable (Filter.Eventually.of_forall hf_le)
  have hf_nonneg : 0 ≤ f := fun x => (mul_pos (energy_filter_critical_overlap_integral_pos_kernel_pos x)
    (energy_filter_critical_overlap_integral_pos_window_integral_pos c x hc)).le
  have hf0 : f 0 ≠ 0 := (mul_pos (energy_filter_critical_overlap_integral_pos_kernel_pos 0)
    (energy_filter_critical_overlap_integral_pos_window_integral_pos c 0 hc)).ne'
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hfc hfi hf_nonneg hf0
