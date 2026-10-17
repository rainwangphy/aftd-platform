import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValuesSorted
import AFTD.Kb.Tcs.SingularValuesSortedNonneg

/-!
# holder_step_for_singularValues

Topic: quantum   Node: 9fb9f16c3d0b

Provenance: formalization of a published result. Source: QuantumInfo, `holder_step_for_singularValues`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The finite-sum Hölder inequality applied to sequences of r-th powers of sorted singular values. With conjugate exponents `p' = p/r > 1` and `q' = q/r > 1` (which satisfy `1/p' + 1/q' = 1` when `1/r = 1/p + 1/q`), this gives: `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}` Note: The sums on the RHS don't depend on the ordering, so we can replace sorted singular values with unsorted ones.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The finite-sum Hölder inequality applied to sequences of r-th powers of sorted singular values. With conjugate exponents `p' = p/r > 1` and `q' = q/r > 1` (which satisfy `1/p' + 1/q' = 1` when `1/r = 1/p + 1/q`), this gives: `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}` Note: The sums on the RHS don't depend on the ordering, so we can replace sorted singular values with unsorted ones. -/
lemma holder_step_for_singularValues (A B : Matrix d d ℂ)
    {r p q : ℝ} (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    (∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r)) ≤
    (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) ^ (r / p) *
    (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ q) ^ (r / q) := by
  have h_holder : (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) * (singularValuesSorted B i ^ r)) ≤ (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) ^ (p / r)) ^ (r / p) * (∑ i : Fin (Fintype.card d), (singularValuesSorted B i ^ r) ^ (q / r)) ^ (r / q) := by
    have := @Real.inner_le_Lp_mul_Lq
    convert @this (Fin (Fintype.card d)) Finset.univ (fun i => singularValuesSorted A i ^ r) (fun i => singularValuesSorted B i ^ r) (p / r) (q / r) _ using 1 <;> norm_num [hr.ne', hp.ne', hq.ne', div_eq_mul_inv]
    · simp only [abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg A _) _),
              abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg B _) _)]
    · constructor <;> norm_num [hr.ne', hp.ne', hq.ne'] at hpqr ⊢ <;> ring_nf at hpqr ⊢ <;> nlinarith [inv_pos.2 hr, inv_pos.2 hp, inv_pos.2 hq, mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hp.ne', mul_inv_cancel₀ hq.ne']
  convert h_holder using 3 <;> push_cast [← Real.rpow_mul (singularValuesSorted_nonneg _ _), mul_div_cancel₀ _ hr.ne'] <;> ring_nf
