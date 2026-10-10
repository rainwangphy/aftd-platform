import AFTD.Prelude

/-!
# Physlib.Wirtinger.fderiv_mul_apply

Topic: classical_mechanics   Node: b93a7335f8f2

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_mul_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The real Fréchet derivative of a product, evaluated at a tangent `v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
omit [NormedSpace ℂ V] in
/-- The real Fréchet derivative of a product, evaluated at a tangent `v`. -/
lemma Physlib.Wirtinger.fderiv_mul_apply {g h : V → ℂ} (hg : DifferentiableAt ℝ g u)
    (hh : DifferentiableAt ℝ h u) (v : V) :
    fderiv ℝ (g * h) u v = g u * fderiv ℝ h u v + h u * fderiv ℝ g u v := by
  simpa using DFunLike.congr_fun (fderiv_mul hg hh) v
