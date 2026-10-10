import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2CFun

/-!
# Fermion.DualLeftHandedWeyl.instAddCommMonoid

Topic: special_relativity   Node: c3ac995f763c

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.instAddCommMonoid`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `AddCommMonoid` on `DualLeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `AddCommMonoid` on `DualLeftHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.DualLeftHandedWeyl.instAddCommMonoid : AddCommMonoid DualLeftHandedWeyl := Equiv.addCommMonoid toFin2ℂFun
