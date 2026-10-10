import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorIsSymmetric
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceSchwartzIncl
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceSchwartzInclInjective
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceParityOperatorUnbounded
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperator
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceParityOperatorSchwartz
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceSchwartzInclInner
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorOfSelfCLMApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceParityOperatorSchwartzParityOperatorSchwartz
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionUnboundedOperatorInstCoeFunForallSubtypeAEEqFunRealComplexVolumeMemAddSubgroupHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBra

/-!
# QuantumMechanics.OneDimension.HilbertSpace.parityOperatorUnbounded_isSymmetric

Topic: quantum_mechanics   Node: d8280c774a4c

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.parityOperatorUnbounded_isSymmetric`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Parity.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.parityOperatorUnbounded_isSymmetric
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
open InnerProductSpace in
lemma QuantumMechanics.OneDimension.HilbertSpace.parityOperatorUnbounded_isSymmetric :
    parityOperatorUnbounded.IsSymmetric := by
  intro ψ1 ψ2
  dsimp [parityOperatorUnbounded]
  rw [schwartzIncl_inner, schwartzIncl_inner]
  let f (x : ℝ) :=
    (starRingEnd ℂ) ((ψ1) (-x)) * (ψ2) x
  change ∫ (x : ℝ), f x = _
  trans ∫ (x : ℝ), f (- x)
  · exact Eq.symm (integral_neg_eq_self f volume)
  · simp only [neg_neg, f]
    rfl
