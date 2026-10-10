import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstNormedAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstModuleComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceLinearEquivEuclidean
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValAdd
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValSmul
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValZero
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceNormEqVal
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInnerEqVal
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstInnerProductSpaceComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstFiniteDimensionalComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstCompleteSpace

/-!
# QuantumMechanics.FiniteHilbertSpace.isometryEquivEuclidean

Topic: quantum_mechanics   Node: 8e001503dfe6

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace.isometryEquivEuclidean`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d` as a linear isometry equivalence, upgrading `linearEquivEuclidean`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.FiniteHilbertSpace in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d` as a linear isometry equivalence, upgrading `linearEquivEuclidean`. -/
noncomputable def QuantumMechanics.FiniteHilbertSpace.isometryEquivEuclidean : FiniteHilbertSpace d ≃ₗᵢ[ℂ] EuclideanSpace ℂ d where
  toLinearEquiv := linearEquivEuclidean
  norm_map' _ := rfl
