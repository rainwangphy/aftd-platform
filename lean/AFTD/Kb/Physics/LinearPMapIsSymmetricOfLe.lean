import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric

/-!
# LinearPMap.IsSymmetric.of_le

Topic: quantum_mechanics   Node: b53576c3a74c

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsSymmetric.of_le`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsSymmetric.of_le
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
lemma LinearPMap.IsSymmetric.of_le (h₁ : T₁.IsSymmetric) (h_le : T₂ ≤ T₁) : T₂.IsSymmetric := by
  intro x y
  have hx : T₂ x = T₁ ⟨x, h_le.1 x.2⟩ := @h_le.2 x ⟨x, h_le.1 x.2⟩ rfl
  have hy : T₂ y = T₁ ⟨y, h_le.1 y.2⟩ := @h_le.2 y ⟨y, h_le.1 y.2⟩ rfl
  exact hx ▸ hy ▸ h₁ ⟨x, h_le.1 x.2⟩ ⟨y, h_le.1 y.2⟩
