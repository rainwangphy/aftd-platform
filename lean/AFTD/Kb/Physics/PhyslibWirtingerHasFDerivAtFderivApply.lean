import AFTD.Prelude

/-!
# Physlib.Wirtinger.hasFDerivAt_fderiv_apply

Topic: classical_mechanics   Node: 3ccb31b7a417

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.hasFDerivAt_fderiv_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The field `p ↦ d_b f` is the evaluation map `· b` composed with `fderiv ℝ f`, so when `fderiv ℝ f` is differentiable its derivative is `fderiv ℝ (fderiv ℝ f) u` post-composed with that evaluation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
omit [NormedSpace ℂ V] in
/-- The field `p ↦ d_b f` is the evaluation map `· b` composed with `fderiv ℝ f`, so when `fderiv ℝ f` is differentiable its derivative is `fderiv ℝ (fderiv ℝ f) u` post-composed with that evaluation. -/
lemma Physlib.Wirtinger.hasFDerivAt_fderiv_apply (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (b : V) :
    HasFDerivAt (fun p => fderiv ℝ f p b)
      ((ContinuousLinearMap.apply ℝ ℂ b).comp (fderiv ℝ (fderiv ℝ f) u)) u :=
  (ContinuousLinearMap.apply ℝ ℂ b).hasFDerivAt.comp u hf'.hasFDerivAt
