import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorOfSelfCLMApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorInstCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra

/-!
# QuantumMechanics.OneDimension.UnboundedOperator.IsGeneralizedEigenvector

Topic: quantum_mechanics   Node: 508748c8f008

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator.IsGeneralizedEigenvector`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A map `F : S →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U` on `S` if there is an eigenvalue `c` such that for all `ψ`, `F (U ψ) = c ⬝ F ψ`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.OneDimension in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι) in
/-- A map `F : S →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U` on `S` if there is an eigenvalue `c` such that for all `ψ`, `F (U ψ) = c ⬝ F ψ` -/
noncomputable def QuantumMechanics.OneDimension.UnboundedOperator.IsGeneralizedEigenvector (F : S →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : S, ∃ ψ' : S, ι ψ' = U ψ ∧ F ψ' = c • F ψ
