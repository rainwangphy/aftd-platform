import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2CAddEquiv

/-!
# Fermion.DualRightHandedWeyl.instModuleComplex

Topic: special_relativity   Node: 0d7e5ed36586

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualRightHandedWeyl.instModuleComplex`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of `Module` on `DualRightHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The instance of `Module` on `DualRightHandedWeyl` defined via its equivalence with `Fin 2 → ℂ`. -/
noncomputable instance Fermion.DualRightHandedWeyl.instModuleComplex : Module ℂ DualRightHandedWeyl := AddEquiv.module ℂ toFin2ℂAddEquiv
