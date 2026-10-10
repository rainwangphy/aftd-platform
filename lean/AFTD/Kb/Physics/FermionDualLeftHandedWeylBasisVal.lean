import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualLeftHandedWeylBasis
import AFTD.Kb.Physics.FermionDualLeftHandedWeylBasisApply

/-!
# Fermion.DualLeftHandedWeyl.basis_val

Topic: special_relativity   Node: c97bafc009d4

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.basis_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fermion.DualLeftHandedWeyl.basis_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Fermion.DualLeftHandedWeyl.basis_val (i : Fin 2) : (basis i).val = Pi.single i 1 := by
  ext j
  simp [basis_apply, Pi.single_apply]
