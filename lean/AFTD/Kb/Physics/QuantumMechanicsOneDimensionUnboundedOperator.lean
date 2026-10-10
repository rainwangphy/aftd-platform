import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.UnboundedOperator

Topic: quantum_mechanics   Node: b60dd142a8fa

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.UnboundedOperator`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Unbounded.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An unbounded operator on the one-dimensional Hilbert space, corresponds to a subobject `ι : S →L[ℂ] HilbertSpace` of the Hilbert space along with the operator `op : S →L[ℂ] HilbertSpace`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open _root_.QuantumMechanics.OneDimension.HilbertSpace in
/-- An unbounded operator on the one-dimensional Hilbert space, corresponds to a subobject `ι : S →L[ℂ] HilbertSpace` of the Hilbert space along with the operator `op : S →L[ℂ] HilbertSpace` -/
@[nolint unusedArguments]
noncomputable def QuantumMechanics.OneDimension.UnboundedOperator {S : Type} [AddCommGroup S] [Module ℂ S]
    [TopologicalSpace S] (ι : S →L[ℂ] HilbertSpace)
    (_ : Function.Injective ι) := S →L[ℂ] HilbertSpace
