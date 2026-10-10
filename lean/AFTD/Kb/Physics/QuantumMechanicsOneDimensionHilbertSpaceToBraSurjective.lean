import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply

/-!
# QuantumMechanics.OneDimension.HilbertSpace.toBra_surjective

Topic: quantum_mechanics   Node: 2ed40cb2b662

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.toBra_surjective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The anti-linear map, `toBra`, taking a ket to it's corresponding bra is surjective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
/-- The anti-linear map, `toBra`, taking a ket to it's corresponding bra is surjective. -/
lemma QuantumMechanics.OneDimension.HilbertSpace.toBra_surjective : Function.Surjective toBra :=
  (InnerProductSpace.toDual ℂ HilbertSpace).surjective
