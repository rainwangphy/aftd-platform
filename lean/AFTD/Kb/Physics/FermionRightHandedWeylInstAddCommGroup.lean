import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylToFin2CFun

/-!
# Fermion.RightHandedWeyl.instAddCommGroup

Topic: special_relativity   Node: e806708a6cb1

Provenance: formalization of a published result. Source: Physlib, `Fermion.RightHandedWeyl.instAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/RightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `AddCommGroup` on `RightHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `AddCommGroup` on `RightHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.RightHandedWeyl.instAddCommGroup : AddCommGroup RightHandedWeyl := Equiv.addCommGroup toFin2ℂFun
