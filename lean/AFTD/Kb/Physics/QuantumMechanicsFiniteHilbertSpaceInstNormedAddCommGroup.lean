import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstModuleComplex
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceLinearEquivEuclidean
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValAdd
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValSmul
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceValZero

/-!
# QuantumMechanics.FiniteHilbertSpace.instNormedAddCommGroup

Topic: quantum_mechanics   Node: 2fac66438348

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace.instNormedAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.FiniteHilbertSpace.instNormedAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.FiniteHilbertSpace in
variable {d : Type*} [Fintype d] [DecidableEq d] in
noncomputable instance QuantumMechanics.FiniteHilbertSpace.instNormedAddCommGroup : NormedAddCommGroup (FiniteHilbertSpace d) :=
  NormedAddCommGroup.induced _ _ linearEquivEuclidean.toLinearMap linearEquivEuclidean.injective
