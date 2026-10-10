import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.UnboundedOperator.instCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace

Topic: quantum_mechanics   Node: 0fc7482552cb

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator.instCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.UnboundedOperator.instCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.OneDimension in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι) in
noncomputable instance QuantumMechanics.OneDimension.UnboundedOperator.instCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace : CoeFun (UnboundedOperator ι hι) (fun _ => S → HilbertSpace) where
  coe := fun U => U.toFun
