import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzCoCModule
import AFTD.Kb.Physics.LorentzCoCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzContrCModuleToFin13C
import AFTD.Kb.Physics.LorentzCoCModuleToFin13C
import AFTD.Kb.Physics.LorentzCoCModuleToFin13CEquiv
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CEquiv
import AFTD.Kb.Physics.LorentzContrCModuleValAdd
import AFTD.Kb.Physics.LorentzContrCModuleValSmul
import AFTD.Kb.Physics.LorentzCoCModuleValAdd
import AFTD.Kb.Physics.LorentzCoCModuleValSmul
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule

/-!
# Lorentz.contrCoContrBi

Topic: special_relativity   Node: 46374cba5e76

Provenance: formalization of a published result. Source: Physlib, `Lorentz.contrCoContrBi`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Contraction.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bi-linear map corresponding to contraction of a contravariant Lorentz vector with a covariant Lorentz vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open CategoryTheory.MonoidalCategory in
/-- The bi-linear map corresponding to contraction of a contravariant Lorentz vector with a covariant Lorentz vector. -/
noncomputable def Lorentz.contrCoContrBi : ContrℂModule →ₗ[ℂ] CoℂModule →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ,
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
