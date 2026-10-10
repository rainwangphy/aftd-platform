import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCentered

/-!
# LinearPMap.covariance

Topic: quantum_mechanics   Node: 2e5c78c02223

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.covariance`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Covariance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Covariance, defined as the real part of the centered inner product.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
/-- Covariance, defined as the real part of the centered inner product. -/
noncomputable def LinearPMap.covariance : ℝ :=
  (⟪centered A ψ, centered B ⟨ψ, hψB⟩⟫_ℂ).re
