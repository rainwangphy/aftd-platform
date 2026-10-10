import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsSymmetric

/-!
# LinearPMap.re_inner_apply_sq_eq_norm_sq

Topic: quantum_mechanics   Node: f392e16f8aac

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.re_inner_apply_sq_eq_norm_sq`. Lean proof by Matteo Cipollina, Krystian Nowakowski, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/StateObservables/Variance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For symmetric `T`, `re ⟪ψ, T(Tψ)⟫` is `‖Tψ‖ ^ 2`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (T : H →ₗ.[ℂ] H) (hT : T.IsSymmetric) in
variable (ψ : T.domain) in
variable (hTψ : T ψ ∈ T.domain) in
variable (hψ_norm : ‖(ψ : H)‖ = 1) in
include hT in
/-- For symmetric `T`, `re ⟪ψ, T(Tψ)⟫` is `‖Tψ‖ ^ 2`. -/
lemma LinearPMap.re_inner_apply_sq_eq_norm_sq :
    (⟪(ψ : H), T ⟨T ψ, hTψ⟩⟫_ℂ).re = ‖T ψ‖ ^ 2 := by
  rw [← hT ψ ⟨T ψ, hTψ⟩, inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]
