import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorOfSelfCLMApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorInstCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra

/-!
# QuantumMechanics.OneDimension.UnboundedOperator.IsSymmetric

Topic: quantum_mechanics   Node: 93aa3b6b31c4

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator.IsSymmetric`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The condition for an unbounded operator to be *symmetric* (equivalently, formally self-adjoint): `⟪U ψ1, ι ψ2⟫ = ⟪ι ψ1, U ψ2⟫` for all `ψ1 ψ2`. This is the Hermitian pairing on the underlying space `S`; on its own it does **not** imply genuine self-adjointness (`A† = A`, including equality of domains), which for an unbounded operator on a proper dense core is strictly stronger.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.OneDimension in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
variable {S : Type} [AddCommGroup S] [Module ℂ S] [TopologicalSpace S]
  {ι : S →L[ℂ] HilbertSpace}
  {hι : Function.Injective ι} (U : UnboundedOperator ι hι) in
open InnerProductSpace in
/-- The condition for an unbounded operator to be *symmetric* (equivalently, formally self-adjoint): `⟪U ψ1, ι ψ2⟫ = ⟪ι ψ1, U ψ2⟫` for all `ψ1 ψ2`. This is the Hermitian pairing on the underlying space `S`; on its own it does **not** imply genuine self-adjointness (`A† = A`, including equality of domains), which for an unbounded operator on a proper dense core is strictly stronger. -/
noncomputable def QuantumMechanics.OneDimension.UnboundedOperator.IsSymmetric : Prop :=
  ∀ ψ1 ψ2 : S, ⟪U ψ1, ι ψ2⟫_ℂ = ⟪ι ψ1, U ψ2⟫_ℂ
