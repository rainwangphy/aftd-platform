import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2CFun

/-!
# Fermion.DualLeftHandedWeyl.toFin2ℂEquiv

Topic: special_relativity   Node: 830bca42532b

Provenance: formalization of a published result. Source: Physlib, `Fermion.DualLeftHandedWeyl.toFin2ℂEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/DualLeftHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between `DualLeftHandedWeyl` and `(Fin 2 → ℂ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The linear equivalence between `DualLeftHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
noncomputable def Fermion.DualLeftHandedWeyl.toFin2ℂEquiv : DualLeftHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
