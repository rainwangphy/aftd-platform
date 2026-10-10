import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceEquivEuclidean
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstModuleComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValAdd
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValSmul
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValZero

/-!
# QuantumMechanics.FiniteHilbertSpace.linearEquivEuclidean

Topic: quantum_mechanics   Node: 47403c0a5e1f

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace.linearEquivEuclidean`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d` as a `ℂ`-linear equivalence, upgrading `equivEuclidean`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.FiniteHilbertSpace in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d` as a `ℂ`-linear equivalence, upgrading `equivEuclidean`. -/
noncomputable def QuantumMechanics.FiniteHilbertSpace.linearEquivEuclidean : FiniteHilbertSpace d ≃ₗ[ℂ] EuclideanSpace ℂ d :=
  { equivEuclidean with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
