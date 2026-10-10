import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.LinearPMapUnitaryConj
import AFTD.Kb.Physics.LinearPMapMapMemUnitaryConjDomain
import AFTD.Kb.Physics.LinearPMapUnitaryConjApplyMap

/-!
# LinearPMap.unitaryConj_sub_smul_surjective

Topic: quantum_mechanics   Node: 2f1df03e097b

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.unitaryConj_sub_smul_surjective`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `A - z` is surjective for a scalar `z : ℂ`, then so is `u A u⁻¹ - z`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
open InnerProductSpace in
open Complex ComplexConjugate in
variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
  {α : Type*} [Fintype α]
  {T T₁ T₂ : H →ₗ.[ℂ] H} {S : α → H →ₗ.[ℂ] H}
  {U U₁ U₂ : H →ₗ.[ℂ] H'} {W : α → H →ₗ.[ℂ] H'}
  {V V₁ V₂ : H' →ₗ.[ℂ] H''} in
variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) in
variable {u A} in
/-- If `A - z` is surjective for a scalar `z : ℂ`, then so is `u A u⁻¹ - z`. -/
lemma LinearPMap.unitaryConj_sub_smul_surjective {z : ℂ} (h : Function.Surjective (A - z • 1).toFun) :
    Function.Surjective (unitaryConj u A - z • 1).toFun := by
  intro φ
  obtain ⟨ξ, hξ⟩ := h (u.symm φ)
  obtain ⟨w, hw⟩ : ∃ w : A.domain, A w - z • (w : H) = u.symm φ :=
    ⟨⟨(ξ : H), (Submodule.mem_inf.mp ξ.2).1⟩, hξ⟩
  refine ⟨⟨u (w : H), Submodule.mem_inf.mpr
    ⟨map_mem_unitaryConj_domain u A w, Submodule.mem_top⟩⟩, ?_⟩
  show unitaryConj u A ⟨u (w : H), map_mem_unitaryConj_domain u A w⟩ - z • (u (w : H)) = φ
  rw [unitaryConj_apply_map, ← _root_.map_smul u, ← _root_.map_sub, hw, u.apply_symm_apply]
