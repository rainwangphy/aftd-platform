import AFTD.Prelude

/-!
# Polynomial.guassian_integrable_polynomial_cons

Topic: classical_mechanics   Node: d0ff1d291d88

Provenance: formalization of a published result. Source: Physlib, `Polynomial.guassian_integrable_polynomial_cons`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.guassian_integrable_polynomial_cons
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[fun_prop]
lemma Polynomial.guassian_integrable_polynomial_cons {b c : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval (c * x)) * Real.exp (-b * x ^ 2) := by
  simp_rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  have h2 : (fun a => P.coeff i • (c * a) ^ i * Real.exp (-b * a ^ 2)) =
      (c ^ i * P.coeff i : ℝ) • (fun x => (x ^ (i : ℝ) * Real.exp (-b * x ^ 2))) := by
    funext x
    simp only [neg_mul, mul_assoc, Real.rpow_natCast, Pi.smul_apply, smul_eq_mul]
    ring
  exact h2 ▸ MeasureTheory.Integrable.smul (c ^ i * P.coeff i : ℝ)
    (integrable_rpow_mul_exp_neg_mul_sq hb (neg_one_lt_zero.trans_le (Nat.cast_nonneg' i)))
