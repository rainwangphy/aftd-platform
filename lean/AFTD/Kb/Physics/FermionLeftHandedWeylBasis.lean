import AFTD.Prelude
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionLeftHandedWeylToFin2CAddEquiv

/-!
# Fermion.LeftHandedWeyl.basis

Topic: special_relativity   Node: a0326579df9e

Provenance: formalization of a published result. Source: Physlib, `Fermion.LeftHandedWeyl.basis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/LeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard basis on left-handed Weyl fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The standard basis on left-handed Weyl fermions. -/
noncomputable def Fermion.LeftHandedWeyl.basis : Basis (Fin 2) ℂ LeftHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ LeftHandedWeyl.toFin2ℂAddEquiv)
