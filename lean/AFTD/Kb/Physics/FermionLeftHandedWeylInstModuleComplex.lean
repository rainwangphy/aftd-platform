import AFTD.Prelude
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionLeftHandedWeylToFin2CAddEquiv

/-!
# Fermion.LeftHandedWeyl.instModuleComplex

Topic: special_relativity   Node: 2c3d0b546f3d

Provenance: formalization of a published result. Source: Physlib, `Fermion.LeftHandedWeyl.instModuleComplex`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/LeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `Module` on `LeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `Module` on `LeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.LeftHandedWeyl.instModuleComplex : Module ℂ LeftHandedWeyl := AddEquiv.module ℂ toFin2ℂAddEquiv
