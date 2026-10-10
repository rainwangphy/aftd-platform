import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2CEquiv

/-!
# Fermion.DualLeftHandedWeyl.toFin2ℂ

Topic: special_relativity   Node: 3d7cd68507f2

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.toFin2ℂ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying element of `Fin 2 → ℂ` of a element in `DualLeftHandedWeyl` defined through the linear equivalence `toFin2ℂEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The underlying element of `Fin 2 → ℂ` of a element in `DualLeftHandedWeyl` defined through the linear equivalence `toFin2ℂEquiv`. -/
noncomputable abbrev Fermion.DualLeftHandedWeyl.toFin2ℂ (ψ : DualLeftHandedWeyl) := toFin2ℂEquiv ψ
