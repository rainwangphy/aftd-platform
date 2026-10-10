import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoCModule
import AFTD.Kb.Physics.LorentzContrCModule
import AFTD.Kb.Physics.LorentzContrCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzContrCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzCoCModuleInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoCModuleInstModuleComplex
import AFTD.Kb.Physics.LorentzContrCoContrBi
import AFTD.Kb.Physics.LorentzCoCModuleToFin13C
import AFTD.Kb.Physics.LorentzContrCModuleToFin13C
import AFTD.Kb.Physics.LorentzCoCModuleToFin13CEquiv
import AFTD.Kb.Physics.LorentzContrCModuleToFin13CEquiv
import AFTD.Kb.Physics.LorentzContrCModuleValAdd
import AFTD.Kb.Physics.LorentzContrCModuleValSmul
import AFTD.Kb.Physics.LorentzCoCModuleValAdd
import AFTD.Kb.Physics.LorentzCoCModuleValSmul
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule

/-!
# Lorentz.contrContrCoBi

Topic: special_relativity   Node: 5d23c9abf8d2

Provenance: formalization of a published result. Source: Physlib, `Lorentz.contrContrCoBi`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/ComplexTensor/Vector/Pre/Contraction.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bi-linear map corresponding to contraction of a covariant Lorentz vector with a contravariant Lorentz vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open CategoryTheory.MonoidalCategory in
/-- The bi-linear map corresponding to contraction of a covariant Lorentz vector with a contravariant Lorentz vector. -/
noncomputable def Lorentz.contrContrCoBi : CoℂModule →ₗ[ℂ] ContrℂModule →ₗ[ℂ] ℂ where
  toFun φ := {
    toFun := fun ψ => φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ,
    map_add' := by
      intro ψ ψ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r ψ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' φ φ' := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r φ := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl
