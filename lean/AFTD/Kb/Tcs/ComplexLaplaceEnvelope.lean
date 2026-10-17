import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplaceIntegrand

/-!
# ComplexLaplaceEnvelope

Topic: quantum   Node: 0ed2d31e42de

Provenance: formalization of a published result. Source: QuantumInfo, `ComplexLaplaceEnvelope`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A two-sided exponential envelope controlling the Laplace integrand near `z`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A two-sided exponential envelope controlling the Laplace integrand near `z`. -/
noncomputable def ComplexLaplaceEnvelope {α : Type*} (E : α → WithTop ℝ) (z : ℂ) (δ : ℝ)
    (x : α) : ℝ :=
  ‖ComplexLaplaceIntegrand E (z - (δ : ℂ)) x‖ +
    ‖ComplexLaplaceIntegrand E (z + (δ : ℂ)) x‖
