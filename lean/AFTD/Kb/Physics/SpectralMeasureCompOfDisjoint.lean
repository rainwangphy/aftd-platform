import AFTD.Prelude
import AFTD.Kb.Physics.SpectralMeasure
import AFTD.Kb.Physics.SpectralMeasureInstCoeVectorMeasure
import AFTD.Kb.Physics.InstIsAddTorsionFreeContinuousLinearMapComplexIdPhyslib
import AFTD.Kb.Physics.SpectralMeasureIsStarProjection
import AFTD.Kb.Physics.SpectralMeasureCompSelf
import AFTD.Kb.Physics.SpectralMeasureUniv
import AFTD.Kb.Physics.SpectralMeasureInstCoeFun
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# SpectralMeasure.comp_of_disjoint

Topic: quantum_mechanics   Node: 247e16306e74

Provenance: formalization of a published result. Source: Physlib, `SpectralMeasure.comp_of_disjoint`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/SpectralMeasure.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpectralMeasure.comp_of_disjoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SpectralMeasure in
open ContinuousLinearMap in
open MeasureTheory in
open Set in
variable {α : Type*} [MeasurableSpace α] in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
variable (μS : SpectralMeasure α H) in
lemma SpectralMeasure.comp_of_disjoint
    {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A ∘L μS B = 0 := by
  suffices μS A ∘L μS (A ∪ B) = μS A by simp_all [μS.of_union]
  refine (IsStarProjection.sub_iff_mul_eq_left (μS.isStarProjection A)
    (μS.isStarProjection (A ∪ B))).mp ?_
  simpa [μS.of_union h hA hB] using μS.isStarProjection B
