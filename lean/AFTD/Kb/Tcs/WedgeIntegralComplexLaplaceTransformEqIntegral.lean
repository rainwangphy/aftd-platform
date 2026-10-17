import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceConvergenceDomain
import AFTD.Kb.Tcs.ComplexLaplaceTransform
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.IntegrableUncurryComplexLaplaceIntegrandHorizontal
import AFTD.Kb.Tcs.IntegrableUncurryComplexLaplaceIntegrandVertical

/-!
# wedgeIntegral_complexLaplaceTransform_eq_integral

Topic: quantum   Node: 61a214c9e182

Provenance: formalization of a published result. Source: QuantumInfo, `wedgeIntegral_complexLaplaceTransform_eq_integral`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

wedgeIntegral_complexLaplaceTransform_eq_integral
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem wedgeIntegral_complexLaplaceTransform_eq_integral
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ}
    {a b : ℂ}
    (hE : Measurable E)
    (hab : Complex.Rectangle a b ⊆ interior (ComplexLaplaceConvergenceDomain E)) :
    Complex.wedgeIntegral a b (ComplexLaplaceTransform E) =
      ∫ x, Complex.wedgeIntegral a b (fun w : ℂ => ComplexLaplaceIntegrand E w x) := by
  have hint {z : ℂ} (hz : z ∈ Complex.Rectangle a b) :
      MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E z) :=
    _root_.interior_subset (s := ComplexLaplaceConvergenceDomain E) (hab hz)
  have ha : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E a) :=
    hint (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hb : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E b) :=
    hint (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hcorner : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand E (b.re + a.im * Complex.I)) :=
    hint (by simp [Complex.Rectangle, Complex.mem_reProdIm])
  have hH := MeasureTheory.intervalIntegral_integral_swap
    (μ := MeasureTheory.volume)
    (f := fun t x => ComplexLaplaceIntegrand E (t + a.im * Complex.I) x)
    (integrable_uncurry_complexLaplaceIntegrand_horizontal hE ha hcorner)
  have hV := MeasureTheory.intervalIntegral_integral_swap
    (μ := MeasureTheory.volume)
    (f := fun t x => ComplexLaplaceIntegrand E (b.re + t * Complex.I) x)
    (integrable_uncurry_complexLaplaceIntegrand_vertical hE hb hcorner)
  simp only [Complex.wedgeIntegral, ComplexLaplaceTransform]
  rw [hH, hV]
  rw [← MeasureTheory.integral_smul, ← MeasureTheory.integral_add]
  · rcases le_total a.re b.re with hab | hba
    · simpa [intervalIntegral.integral_of_le hab, Function.uncurry, Set.uIoc_of_le hab]
        using (integrable_uncurry_complexLaplaceIntegrand_horizontal hE ha hcorner).integral_prod_right
    · simpa [intervalIntegral.integral_of_ge hba, Function.uncurry, Set.uIoc_of_ge hba]
        using (integrable_uncurry_complexLaplaceIntegrand_horizontal hE ha hcorner).integral_prod_right.neg
  · refine (?_ : MeasureTheory.Integrable _ MeasureTheory.volume).smul Complex.I
    rcases le_total a.im b.im with hab | hba
    · simpa [intervalIntegral.integral_of_le hab, Function.uncurry, Set.uIoc_of_le hab]
        using (integrable_uncurry_complexLaplaceIntegrand_vertical hE hb hcorner).integral_prod_right
    · simpa [intervalIntegral.integral_of_ge hba, Function.uncurry, Set.uIoc_of_ge hba]
        using (integrable_uncurry_complexLaplaceIntegrand_vertical hE hb hcorner).integral_prod_right.neg
