import AFTD.Prelude
import AFTD.Kb.Physics.SpectralMeasure
import AFTD.Kb.Physics.SpectralMeasureInstCoeVectorMeasure
import AFTD.Kb.Physics.SpectralMeasureInstCoeFun
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# SpectralMeasure.univ

Topic: quantum_mechanics   Node: 5f2a3cf6a9b0

Provenance: formalization of a published result. Source: Physlib, `SpectralMeasure.univ`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/SpectralMeasure.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SpectralMeasure.univ
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
@[simp]
lemma SpectralMeasure.univ : μS univ = 1 := μS.univ'
