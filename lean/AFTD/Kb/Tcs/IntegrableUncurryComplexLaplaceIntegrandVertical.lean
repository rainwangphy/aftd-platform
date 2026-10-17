import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.MeasurableComplexLaplaceIntegrand
import AFTD.Kb.Tcs.NormComplexLaplaceIntegrandVerticalLeEndpointEnvelope

/-!
# integrable_uncurry_complexLaplaceIntegrand_vertical

Topic: quantum   Node: 9e5e9bee4b64

Provenance: formalization of a published result. Source: QuantumInfo, `integrable_uncurry_complexLaplaceIntegrand_vertical`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

integrable_uncurry_complexLaplaceIntegrand_vertical
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem integrable_uncurry_complexLaplaceIntegrand_vertical
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ}
    {a b : ℂ}
    (hE : Measurable E)
    (hb : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E b))
    (hba : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand E (b.re + a.im * Complex.I))) :
    MeasureTheory.Integrable
      (Function.uncurry fun t : ℝ => fun x : α =>
        ComplexLaplaceIntegrand E (b.re + t * Complex.I) x)
      ((MeasureTheory.volume.restrict (Set.uIoc a.im b.im)).prod MeasureTheory.volume) := by
  let μI := MeasureTheory.volume.restrict (Set.uIoc a.im b.im)
  have : MeasureTheory.IsFiniteMeasure μI := ⟨by
    rw [MeasureTheory.Measure.restrict_apply_univ]
    simp [Set.uIoc]⟩
  have hsm : MeasureTheory.StronglyMeasurable (Function.uncurry fun t : ℝ => fun x : α =>
      ComplexLaplaceIntegrand E (b.re + t * Complex.I) x) := by
    refine MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable ?_ ?_
    · intro x
      unfold ComplexLaplaceIntegrand
      split_ifs <;> fun_prop
    · intro t
      exact (measurable_complexLaplaceIntegrand hE (b.re + t * Complex.I)).stronglyMeasurable
  refine ((hb.norm.add hba.norm).comp_snd μI).mono'
    hsm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p =>
    norm_complexLaplaceIntegrand_vertical_le_endpointEnvelope (a := a) (b := b) (t := p.1) p.2
