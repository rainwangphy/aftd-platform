import AFTD.Prelude
import AFTD.Kb.Physics.FermionDualRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeyl
import AFTD.Kb.Physics.FermionRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2C
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstAddCommMonoid
import AFTD.Kb.Physics.FermionDualRightHandedWeylInstModuleComplex
import AFTD.Kb.Physics.FermionRightHandedWeylToFin2C
import AFTD.Kb.Physics.FermionDualRightHandedWeylToFin2CEquiv
import AFTD.Kb.Physics.FermionLeftDualBi
import AFTD.Kb.Physics.FermionRightHandedWeylToFin2CEquiv
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule

/-!
# Fermion.dualRightBi

Topic: special_relativity   Node: 1e6286c0e667

Provenance: formalization of a published result. Source: Physlib, `Fermion.dualRightBi`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/Contraction.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bi-linear map corresponding to contraction of a dual-right-handed Weyl fermion with a right-handed Weyl fermion.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
/-- The bi-linear map corresponding to contraction of a dual-right-handed Weyl fermion with a right-handed Weyl fermion. -/
noncomputable def Fermion.dualRightBi : DualRightHandedWeyl →ₗ[ℂ] RightHandedWeyl →ₗ[ℂ] ℂ where
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
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
