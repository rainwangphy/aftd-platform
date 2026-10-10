import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric
import AFTD.Kb.Physics.LinearPMapInnerMapPolarization
import AFTD.Kb.Physics.LinearPMapInnerMapPolarization'

/-!
# LinearPMap.isSymmetric_iff_inner_map_self_real

Topic: quantum_mechanics   Node: 67caf7f2436e

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.isSymmetric_iff_inner_map_self_real`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.isSymmetric_iff_inner_map_self_real
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
lemma LinearPMap.isSymmetric_iff_inner_map_self_real :
    T.IsSymmetric ↔ ∀ x : T.domain, conj ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  refine ⟨fun h_symm x ↦ by simp [h_symm x x], fun h_re x y ↦ ?_⟩
  nth_rw 2 [← inner_conj_symm, inner_map_polarization]
  simp only [map_div₀, _root_.map_sub, _root_.map_add, map_mul, neg_mul, conj_ofNat, conj_I, h_re]
  rw [inner_map_polarization']
  simp [sub_eq_add_neg]
