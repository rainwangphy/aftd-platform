import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFGenerator

/-!
# subadditive_f_generator_hasDerivAt

Topic: information   Node: 0bb9b5a40499

Provenance: helper lemma. helper for arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1 (equation (4))

For s continuous on (0, ∞) and y > 0, the generator f(x) = α x log x + ∫_1^x (x - t) s(t)/t² dt has derivative f'(y) = α (log y + 1) + ∫_1^y s(t)/t² dt.
-/

theorem subadditive_f_generator_hasDerivAt (α : ℝ) (s : ℝ → ℝ)
    (hs : ContinuousOn s (Set.Ioi 0)) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (subadditive_f_generator α s)
      (α * (Real.log y + 1) + ∫ t in (1 : ℝ)..y, s t / t ^ 2) y := by
  have ho : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hcs1 : ContinuousOn (fun t => s t / t ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div hs (continuousOn_id.pow 2)
    intro t ht; rw [Set.mem_Ioi] at ht; exact ne_of_gt (pow_pos ht 2)
  have hcs2 : ContinuousOn (fun t => t * s t / t ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div (continuousOn_id.mul hs) (continuousOn_id.pow 2)
    intro t ht; rw [Set.mem_Ioi] at ht; exact ne_of_gt (pow_pos ht 2)
  have h_deriv_integral : ∀ (f : ℝ → ℝ), ContinuousOn f (Set.Ioi 0) →
      HasDerivAt (fun u => ∫ t in (1 : ℝ)..u, f t) (f y) y := by
    intro f hf
    have hsub : Set.uIcc 1 y ⊆ Set.Ioi 0 := by
      intro t ht
      rw [Set.mem_Ioi]
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hint : IntervalIntegrable f MeasureTheory.volume 1 y :=
      (hf.mono hsub).intervalIntegrable
    have hfc : ∀ x ∈ Set.Ioi (0 : ℝ), ContinuousAt f x := fun x hx => hf.continuousAt (ho.mem_nhds hx)
    have hmeas : StronglyMeasurableAtFilter f (nhds y) MeasureTheory.volume :=
      ContinuousAt.stronglyMeasurableAtFilter ho hfc y hy
    have hconty : ContinuousAt f y := hfc y hy
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hconty
  have hf1 : HasDerivAt (fun x => ∫ t in (1 : ℝ)..x, s t / t ^ 2) (s y / y ^ 2) y :=
    h_deriv_integral (fun t => s t / t ^ 2) hcs1
  have hf2 : HasDerivAt (fun x => ∫ t in (1 : ℝ)..x, t * s t / t ^ 2) (y * s y / y ^ 2) y :=
    h_deriv_integral (fun t => t * s t / t ^ 2) hcs2
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0
  have hid : HasDerivAt (fun x => x) 1 y := hasDerivAt_id y
  have hmul : HasDerivAt (fun x => x * Real.log x) (1 * Real.log y + y * y⁻¹) y := hid.mul hlog
  rw [mul_inv_cancel₀ hy0, one_mul] at hmul
  have hα : HasDerivAt (fun x => α * x * Real.log x) (α * (Real.log y + 1)) y := by
    simpa only [mul_assoc] using hmul.const_mul α
  have hprod : HasDerivAt (fun x => x * (∫ t in (1 : ℝ)..x, s t / t ^ 2))
      (1 * (∫ t in (1 : ℝ)..y, s t / t ^ 2) + y * (s y / y ^ 2)) y := hid.mul hf1
  have hsub_deriv : HasDerivAt (fun x => x * (∫ t in (1 : ℝ)..x, s t / t ^ 2) - ∫ t in (1 : ℝ)..x, t * s t / t ^ 2)
      (∫ t in (1 : ℝ)..y, s t / t ^ 2) y := by
    have h := hprod.sub hf2
    have hr : (1 * (∫ t in (1 : ℝ)..y, s t / t ^ 2) + y * (s y / y ^ 2)) - (y * s y / y ^ 2) =
        ∫ t in (1 : ℝ)..y, s t / t ^ 2 := by ring
    rw [hr] at h
    exact h
  have htot : HasDerivAt (fun x => α * x * Real.log x + (x * (∫ t in (1 : ℝ)..x, s t / t ^ 2) - ∫ t in (1 : ℝ)..x, t * s t / t ^ 2))
      (α * (Real.log y + 1) + ∫ t in (1 : ℝ)..y, s t / t ^ 2) y := hα.add hsub_deriv
  have heq : subadditive_f_generator α s =ᶠ[nhds y]
      fun x => α * x * Real.log x + (x * (∫ t in (1 : ℝ)..x, s t / t ^ 2) - ∫ t in (1 : ℝ)..x, t * s t / t ^ 2) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨Set.Ioi 0, ho.mem_nhds hy, fun x hx => ?_⟩
    dsimp [subadditive_f_generator]
    congr 1
    have hxpos : 0 < x := hx
    have hsubx : Set.uIcc 1 x ⊆ Set.Ioi 0 := by
      intro t ht
      rw [Set.mem_Ioi]
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have h1 : IntervalIntegrable (fun t => x * (s t / t ^ 2)) MeasureTheory.volume 1 x :=
      ((continuousOn_const.mul hcs1).mono hsubx).intervalIntegrable
    have h2 : IntervalIntegrable (fun t => t * s t / t ^ 2) MeasureTheory.volume 1 x :=
      (hcs2.mono hsubx).intervalIntegrable
    have h_integrand : (fun t => (x - t) * s t / t ^ 2) = fun t => x * (s t / t ^ 2) - t * s t / t ^ 2 := by
      ext t; ring
    rw [h_integrand]
    rw [intervalIntegral.integral_sub h1 h2]
    rw [intervalIntegral.integral_const_mul]
  exact htot.congr_of_eventuallyEq heq
