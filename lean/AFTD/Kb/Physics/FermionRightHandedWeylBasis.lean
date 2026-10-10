import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionRightHandedWeylToFin2CAddEquiv

/-!
# Fermion.RightHandedWeyl.basis

Topic: special_relativity   Node: d6e401cea3f7

Provenance: formalization of a published result. Source: Physlib, `Fermion.RightHandedWeyl.basis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/RightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard basis on right-handed Weyl fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The standard basis on right-handed Weyl fermions. -/
noncomputable def Fermion.RightHandedWeyl.basis : Basis (Fin 2) ℂ RightHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ RightHandedWeyl.toFin2ℂAddEquiv)
