import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFGenerator
import AFTD.Kb.Tcs.SubadditiveFGeneratorHasDerivAt

/-!
# subadditive_f_generator_deriv2

Topic: information   Node: f6287bcac4e2

Provenance: helper lemma. helper for arXiv:2610.21231 (On the subadditivity of mutual f-information), Corollary 1 (equation (4) integrates x² f''(x) = g(x) = α x + s(x))

For s continuous on (0, ∞) and y > 0, the derivative of the generator f of equation (4) has derivative α/y + s(y)/y² at y, i.e. f''(y) = α/y + s(y)/y², so y² f''(y) = α y + s(y).
-/

theorem subadditive_f_generator_deriv2 (α : ℝ) (s : ℝ → ℝ)
    (hs : ContinuousOn s (Set.Ioi 0)) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (subadditive_f_generator α s)) (α / y + s y / y ^ 2) y := by
  have ho : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hcs1 : ContinuousOn (fun t => s t / t ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div hs (continuousOn_id.pow 2)
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
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hlog : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0
  have hlog1 : HasDerivAt (fun x => Real.log x + 1) y⁻¹ y := by
    simpa using hlog.add_const 1
  have hα : HasDerivAt (fun x => α * (Real.log x + 1)) (α / y) y := by
    have h := hlog1.const_mul α
    have hr : α * y⁻¹ = α / y := by ring
    rwa [hr] at h
  have hsum : HasDerivAt (fun x => α * (Real.log x + 1) + ∫ t in (1 : ℝ)..x, s t / t ^ 2)
      (α / y + s y / y ^ 2) y := hα.add hf1
  have heq : deriv (subadditive_f_generator α s) =ᶠ[nhds y]
      fun x => α * (Real.log x + 1) + ∫ t in (1 : ℝ)..x, s t / t ^ 2 := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨Set.Ioi 0, ho.mem_nhds hy, fun x hx => ?_⟩
    exact (subadditive_f_generator_hasDerivAt α s hs hx).deriv
  exact hsum.congr_of_eventuallyEq heq
