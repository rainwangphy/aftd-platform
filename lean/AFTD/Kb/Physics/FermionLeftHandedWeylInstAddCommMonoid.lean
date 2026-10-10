import AFTD.Prelude
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionLeftHandedWeylToFin2CFun

/-!
# Fermion.LeftHandedWeyl.instAddCommMonoid

Topic: special_relativity   Node: 07c50bbe5dd7

Provenance: formalization of a published result. Source: Physlib, `Fermion.LeftHandedWeyl.instAddCommMonoid`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/LeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `AddCommMonoid` on `LeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `AddCommMonoid` on `LeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.LeftHandedWeyl.instAddCommMonoid : AddCommMonoid LeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun
