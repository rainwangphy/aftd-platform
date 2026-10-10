import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstAddCommGroup
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpaceInstModuleComplex

/-!
# QuantumMechanics.FiniteHilbertSpace.val_add

Topic: quantum_mechanics   Node: 6866eee051ce

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace.val_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.FiniteHilbertSpace.val_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics QuantumMechanics.FiniteHilbertSpace in
variable {d : Type*} [Fintype d] [DecidableEq d] in
@[simp]
lemma QuantumMechanics.FiniteHilbertSpace.val_add (ψ φ : FiniteHilbertSpace d) : (ψ + φ).val = ψ.val + φ.val := rfl
