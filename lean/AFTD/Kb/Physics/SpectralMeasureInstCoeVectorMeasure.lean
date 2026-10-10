import AFTD.Prelude
import AFTD.Kb.Physics.SpectralMeasure
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# SpectralMeasure.instCoeVectorMeasure

Topic: quantum_mechanics   Node: 17bf4a130a5d

Provenance: formalization of a published result. Source: Physlib, `SpectralMeasure.instCoeVectorMeasure`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/SpectralMeasure.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpectralMeasure.instCoeVectorMeasure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
open MeasureTheory in
open Set in
variable {α : Type*} [MeasurableSpace α] in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
variable (μS : SpectralMeasure α H) in
noncomputable instance SpectralMeasure.instCoeVectorMeasure : Coe (SpectralMeasure α H) (VectorMeasure α (H →L[ℂ] H)) :=
  ⟨toVectorMeasure⟩
