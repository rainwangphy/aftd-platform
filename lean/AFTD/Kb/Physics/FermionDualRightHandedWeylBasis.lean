import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2CAddEquiv
import AFTD.Kb.Physics.FermionRightHandedWeylBasis

/-!
# Fermion.DualRightHandedWeyl.basis

Topic: special_relativity   Node: 9bed017c2031

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualRightHandedWeyl.basis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard basis on dual-right-handed Weyl fermions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The standard basis on dual-right-handed Weyl fermions. -/
noncomputable def Fermion.DualRightHandedWeyl.basis : Basis (Fin 2) ℂ DualRightHandedWeyl := Basis.ofEquivFun
  (AddEquiv.linearEquiv ℂ DualRightHandedWeyl.toFin2ℂAddEquiv)
