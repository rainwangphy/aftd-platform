import AFTD.Prelude
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylToFin2CFun
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionRightHandedWeylInstModuleComplex

/-!
# Fermion.RightHandedWeyl.toFin2ℂEquiv

Topic: special_relativity   Node: df1e12e34738

Provenance: formalization of a published result. Source: Physlib, `Fermion.RightHandedWeyl.toFin2ℂEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/RightHanded.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The linear equivalence between `RightHandedWeyl` and `(Fin 2 → ℂ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The linear equivalence between `RightHandedWeyl` and `(Fin 2 → ℂ)`. -/
@[simps!]
noncomputable def Fermion.RightHandedWeyl.toFin2ℂEquiv : RightHandedWeyl ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun := toFin2ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin2ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
