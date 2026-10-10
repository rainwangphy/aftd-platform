import AFTD.Prelude
import AFTD.Kb.Physics.FermionLeftHandedWeyl
import AFTD.Kb.Physics.FermionDualLeftHandedWeyl
import AFTD.Kb.Physics.FermionLeftHandedWeylToFin2C
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2C
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualLeftHandedWeylToFin2CEquiv
import AFTD.Kb.Physics.FermionLeftHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionLeftHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionLeftHandedWeylToFin2CEquiv
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule

/-!
# Fermion.leftDualBi

Topic: special_relativity   Node: c6918582cead

Provenance: formalization of a published result. Source: Physlib, `Fermion.leftDualBi`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/Contraction.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bi-linear map corresponding to contraction of a left-handed Weyl fermion with a dual-left-handed Weyl fermion.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The bi-linear map corresponding to contraction of a left-handed Weyl fermion with a dual-left-handed Weyl fermion. -/
noncomputable def Fermion.leftDualBi : LeftHandedWeyl →ₗ[ℂ] DualLeftHandedWeyl →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl
