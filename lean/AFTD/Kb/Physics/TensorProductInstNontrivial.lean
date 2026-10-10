import AFTD.Prelude

/-!
# TensorProduct.instNontrivial

Topic: quantum_mechanics   Node: 09eb2d3146b4

Provenance: formalization of a published result. Source: Physlib, `TensorProduct.instNontrivial`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/TensorProducts/CompleteTensorProduct.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorProduct.instNontrivial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UniformSpace in
open scoped InnerProductSpace TensorProduct in
variable (𝕜 : Type*) [RCLike 𝕜] in
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] in
variable [Nontrivial E] [Nontrivial F] in
noncomputable instance TensorProduct.instNontrivial : Nontrivial (E ⊗[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    exact ⟨x ⊗ₜ y, 0, norm_pos_iff.mp (by simp [hx, hy])⟩
