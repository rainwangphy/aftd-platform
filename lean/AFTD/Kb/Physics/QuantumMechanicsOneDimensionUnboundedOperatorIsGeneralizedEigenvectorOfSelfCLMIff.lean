import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorIsGeneralizedEigenvector
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorOfSelfCLM
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorOfSelfCLMApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorInstCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra

/-!
# QuantumMechanics.OneDimension.UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff

Topic: quantum_mechanics   Node: 24ebe3c6d7be

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.OneDimension QuantumMechanics.OneDimension.UnboundedOperator in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι) in
lemma QuantumMechanics.OneDimension.UnboundedOperator.isGeneralizedEigenvector_ofSelfCLM_iff {Op : S →L[ℂ] S}
    (F : S →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSelfCLM (hι := hι) Op) F c ↔
    ∀ ψ : S, F (Op ψ) = c • F ψ := by
  simp only [IsGeneralizedEigenvector, ofSelfCLM_apply, hι.eq_iff, exists_eq_left]
