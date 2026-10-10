import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapCovariance
import AFTD.Kb.Physics.LinearPMapVariance
import AFTD.Kb.Physics.LinearPMapCentered
import AFTD.Kb.Physics.LinearPMapCovarianceEqReInnerCentered
import AFTD.Kb.Physics.LinearPMapVarianceEqCenteredNormSq
import AFTD.Kb.Physics.LinearPMapStandardDeviationSq

/-!
# LinearPMap.covariance_self_eq_variance

Topic: quantum_mechanics   Node: 98c4b38507c1

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.covariance_self_eq_variance`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/Covariance.lean (Copyright (c) 2026 Axiomatic-AI. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.covariance_self_eq_variance
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open InnerProductSpace in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
variable (A B : H →ₗ.[ℂ] H) in
variable (ψ : A.domain) in
variable (hψB : (ψ : H) ∈ B.domain) in
@[simp]
lemma LinearPMap.covariance_self_eq_variance (A : H →ₗ.[ℂ] H) (ψ : A.domain) :
    covariance A A ψ (by exact ψ.2) = variance A ψ := by
  rw [covariance_eq_re_inner_centered, variance_eq_centered_norm_sq, inner_self_eq_norm_sq_to_K]
  rw [sq, sq, Complex.mul_re]
  simp [Complex.ofReal_re, Complex.ofReal_im]
