import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand
import AFTD.Kb.Tcs.MeasurableComplexLaplaceIntegrand
import AFTD.Kb.Tcs.ComplexLaplaceEndpointEnvelope
import AFTD.Kb.Tcs.NormComplexLaplaceIntegrandHorizontalLeEndpointEnvelope

/-!
# integrable_uncurry_complexLaplaceIntegrand_horizontal

Topic: quantum   Node: 4df86aee0ad1

Provenance: formalization of a published result. Source: QuantumInfo, `integrable_uncurry_complexLaplaceIntegrand_horizontal`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

integrable_uncurry_complexLaplaceIntegrand_horizontal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
theorem integrable_uncurry_complexLaplaceIntegrand_horizontal
    {α : Type*} [MeasureTheory.MeasureSpace α]
    [MeasureTheory.SFinite (MeasureTheory.volume : MeasureTheory.Measure α)] {E : α → WithTop ℝ}
    {a b : ℂ}
    (hE : Measurable E)
    (ha : MeasureTheory.Integrable (μ := MeasureTheory.volume) (ComplexLaplaceIntegrand E a))
    (hb : MeasureTheory.Integrable (μ := MeasureTheory.volume)
      (ComplexLaplaceIntegrand E (b.re + a.im * Complex.I))) :
    MeasureTheory.Integrable
      (Function.uncurry fun t : ℝ => fun x : α =>
        ComplexLaplaceIntegrand E (t + a.im * Complex.I) x)
      ((MeasureTheory.volume.restrict (Set.uIoc a.re b.re)).prod MeasureTheory.volume) := by
  let μI := MeasureTheory.volume.restrict (Set.uIoc a.re b.re)
  have : MeasureTheory.IsFiniteMeasure μI := ⟨by
    rw [MeasureTheory.Measure.restrict_apply_univ]
    simp [Set.uIoc]⟩
  have hsm : MeasureTheory.StronglyMeasurable (Function.uncurry fun t : ℝ => fun x : α =>
      ComplexLaplaceIntegrand E (t + a.im * Complex.I) x) := by
    refine MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable ?_ ?_
    · intro x
      unfold ComplexLaplaceIntegrand
      split_ifs <;> fun_prop
    · intro t
      exact (measurable_complexLaplaceIntegrand hE (t + a.im * Complex.I)).stronglyMeasurable
  have henv : MeasureTheory.Integrable
      (fun p : ℝ × α => ComplexLaplaceEndpointEnvelope E a (b.re + a.im * Complex.I) p.2)
      (μI.prod MeasureTheory.volume) :=
    (ha.norm.add hb.norm).comp_snd μI
  refine henv.mono' hsm.aestronglyMeasurable ?_
  simp only [Function.uncurry]
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_le
    (show Measurable fun p : ℝ × α =>
      ‖ComplexLaplaceIntegrand E (p.1 + a.im * Complex.I) p.2‖ from hsm.measurable.norm)
    (show Measurable fun p : ℝ × α =>
      ComplexLaplaceEndpointEnvelope E a (b.re + a.im * Complex.I) p.2 from
        ((measurable_complexLaplaceIntegrand hE a).norm.add
          (measurable_complexLaplaceIntegrand hE (b.re + a.im * Complex.I)).norm).comp measurable_snd))]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
  exact Filter.Eventually.of_forall fun x =>
    norm_complexLaplaceIntegrand_horizontal_le_endpointEnvelope (Set.uIoc_subset_uIcc ht) x
