import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2CAddEquiv
import AFTD.Kb.Physics.FermionRightHandedWeylBasis

/-!
# Fermion.DualLeftHandedWeyl.basis

Topic: special_relativity   Node: 3703046317b4

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.basis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard basis on dual-left-handed Weyl fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The standard basis on dual-left-handed Weyl fermions. -/
noncomputable def Fermion.DualLeftHandedWeyl.basis : Basis (Fin 2) ℂ DualLeftHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ DualLeftHandedWeyl.toFin2ℂAddEquiv)
