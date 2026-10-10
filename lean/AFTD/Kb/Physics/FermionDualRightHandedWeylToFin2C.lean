import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2CEquiv

/-!
# Fermion.DualRightHandedWeyl.toFin2ℂ

Topic: special_relativity   Node: f7e37529d955

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualRightHandedWeyl.toFin2ℂ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualRightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying element of `Fin 2 → ℂ` of a element in `DualRightHandedWeyl` defined through the linear equivalence `toFin2ℂEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The underlying element of `Fin 2 → ℂ` of a element in `DualRightHandedWeyl` defined through the linear equivalence `toFin2ℂEquiv`. -/
noncomputable abbrev Fermion.DualRightHandedWeyl.toFin2ℂ (ψ : DualRightHandedWeyl) := toFin2ℂEquiv ψ
