import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorOfSelfCLM
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorInstCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra

/-!
# QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM_apply

Topic: quantum_mechanics   Node: 5eedb3d446cc

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.OneDimension QuantumMechanics.OneDimension.UnboundedOperator in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι) in
@[simp]
lemma QuantumMechanics.OneDimension.UnboundedOperator.ofSelfCLM_apply (Op : S →L[ℂ] S) (ψ : S) :
    ofSelfCLM (hι := hι) Op ψ = ι (Op ψ) := rfl
