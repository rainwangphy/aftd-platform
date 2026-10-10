import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionRightHandedWeylBasis
import AFTD.Kb.Physics.FermionRightHandedWeylBasisApply

/-!
# Fermion.RightHandedWeyl.basis_val

Topic: special_relativity   Node: f44cfe7fe34d

Provenance: formalization of a published result. Source: Physlib, `Fermion.RightHandedWeyl.basis_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/RightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.RightHandedWeyl.basis_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Fermion.RightHandedWeyl.basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]
