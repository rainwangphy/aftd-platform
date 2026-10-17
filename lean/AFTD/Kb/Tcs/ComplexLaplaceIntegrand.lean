import AFTD.Prelude

/-!
# ComplexLaplaceIntegrand

Topic: quantum   Node: d0ff3a4f7a52

Provenance: formalization of a published result. Source: QuantumInfo, `ComplexLaplaceIntegrand`. Lean proof by Dennj Osele, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ComplexLaplaceTransform.lean (Copyright (c) 2025 Dennj Osele. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The integrand of the complex Laplace transform of a possibly infinite-valued energy function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The integrand of the complex Laplace transform of a possibly infinite-valued energy function. -/
noncomputable def ComplexLaplaceIntegrand {α : Type*} (E : α → WithTop ℝ) (z : ℂ) (x : α) : ℂ :=
  if h : E x = ⊤ then 0 else Complex.exp (-z * (E x).untop h : ℂ)
