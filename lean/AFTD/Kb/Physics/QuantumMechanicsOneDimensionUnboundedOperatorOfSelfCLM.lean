import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorInstCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra
import AFTD.Kb.Tcs.KnillLaflamme

/-!
# QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM

Topic: quantum_mechanics   Node: 6e502d65b602

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An unbounded operator created from a continuous linear map ` S →L[ℂ] S`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.OneDimension in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι) in
/-- An unbounded operator created from a continuous linear map ` S →L[ℂ] S`. -/
noncomputable def QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM (Op : S →L[ℂ] S) : UnboundedOperator ι hι := ι ∘L Op
