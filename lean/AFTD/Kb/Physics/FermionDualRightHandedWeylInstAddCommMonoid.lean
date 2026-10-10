import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2CFun

/-!
# Fermion.DualRightHandedWeyl.instAddCommMonoid

Topic: special_relativity   Node: 78a17a1f8073

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualRightHandedWeyl.instAddCommMonoid`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `AddCommMonoid` on `DualRightHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `AddCommMonoid` on `DualRightHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.DualRightHandedWeyl.instAddCommMonoid : AddCommMonoid DualRightHandedWeyl := Equiv.addCommMonoid toFin2ℂFun
