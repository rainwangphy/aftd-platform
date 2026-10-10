import AFTD.Prelude
import AFTD.Kb.Physics.SpectralMeasure
import AFTD.Kb.Physics.SpectralMeasureInstCoeVectorMeasure
import AFTD.Kb.Physics.SpectralMeasureCompOfDisjoint
import AFTD.Kb.Physics.SpectralMeasureCompSelf
import AFTD.Kb.Physics.SpectralMeasureUniv
import AFTD.Kb.Physics.SpectralMeasureInstCoeFun
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# SpectralMeasure.comp_eq_of_inter

Topic: quantum_mechanics   Node: 3798f93fa0b2

Provenance: formalization of a published result. Source: Physlib, `SpectralMeasure.comp_eq_of_inter`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/SpectralMeasure.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpectralMeasure.comp_eq_of_inter
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
lemma SpectralMeasure.comp_eq_of_inter {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A ∘L μS B = μS (A ∩ B) := by
  nth_rw 1 [← inter_union_sdiff B A, ← inter_union_sdiff A B]
  simp only [μS.of_union, hA.inter hB, hB.inter hA, hA.diff hB, hB.diff hA,
    disjoint_sdiff_inter.symm, add_comp, comp_add]
  rw [inter_comm B A, μS.comp_of_disjoint disjoint_sdiff_inter (hA.diff hB) (hA.inter hB),
    inter_comm A B, μS.comp_of_disjoint disjoint_sdiff_inter.symm (hB.inter hA) (hB.diff hA)]
  simp [μS.comp_of_disjoint disjoint_sdiff_sdiff (hA.diff hB) (hB.diff hA)]
