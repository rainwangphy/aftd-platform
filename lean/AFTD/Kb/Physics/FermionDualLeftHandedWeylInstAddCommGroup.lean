import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2CFun

/-!
# Fermion.DualLeftHandedWeyl.instAddCommGroup

Topic: special_relativity   Node: 78a64af3f27a

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.instAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `AddCommGroup` on `DualLeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `AddCommGroup` on `DualLeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.DualLeftHandedWeyl.instAddCommGroup : AddCommGroup DualLeftHandedWeyl := Equiv.addCommGroup toFin2ℂFun
