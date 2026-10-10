import AFTD.Prelude

/-!
# LinearMap.continuous_iff_bounded

Topic: quantum_mechanics   Node: 59c65d22ee9a

Provenance: formalization of a published result. Source: Physlib, `LinearMap.continuous_iff_bounded`. Lean proof by Adam Bornemann, Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Unbounded.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`f : E →ₗ[𝕜] F` is continuous iff there exists `M > 0` s.t. `‖f x‖ ≤ M * ‖x‖` for all `x : E`. This is a (convenient) immediate consequence of `IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
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
/-- `f : E →ₗ[𝕜] F` is continuous iff there exists `M > 0` s.t. `‖f x‖ ≤ M * ‖x‖` for all `x : E`. This is a (convenient) immediate consequence of `IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap`. -/
lemma LinearMap.continuous_iff_bounded {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →ₗ[𝕜] F} : Continuous f ↔ ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖ := by
  refine (and_congr_right_iff (a := IsLinearMap 𝕜 f)).mp ?_ f.isLinear
  rw [← isBoundedLinearMap_iff]
  exact IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap f
