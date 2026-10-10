import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceEquivEuclidean
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstAddCommGroup

/-!
# QuantumMechanics.FiniteHilbertSpace.instModuleComplex

Topic: quantum_mechanics   Node: 404fc3f64587

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace.instModuleComplex`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.FiniteHilbertSpace.instModuleComplex
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.FiniteHilbertSpace in
variable {d : Type*} [Fintype d] [DecidableEq d] in
noncomputable instance QuantumMechanics.FiniteHilbertSpace.instModuleComplex : Module ℂ (FiniteHilbertSpace d) :=
  AddEquiv.module ℂ { equivEuclidean with map_add' := fun _ _ => rfl }
