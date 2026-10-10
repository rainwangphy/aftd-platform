import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsClosableSmul

/-!
# LinearPMap.IsClosable.smul_iff

Topic: quantum_mechanics   Node: f4c9bd5af55f

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsClosable.smul_iff`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.IsClosable.smul_iff
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
lemma LinearPMap.IsClosable.smul_iff {c : ℂ} (hc : c ≠ 0) : (c • U).IsClosable ↔ U.IsClosable :=
  ⟨fun h ↦ one_smul ℂ U ▸ inv_mul_cancel₀ hc ▸ smul_smul c⁻¹ c U ▸ h.smul c⁻¹, fun h ↦ h.smul c⟩
