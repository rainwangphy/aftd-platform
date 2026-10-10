import AFTD.Prelude

/-!
# Physlib.Wirtinger.fderiv_star_eq

Topic: classical_mechanics   Node: 3490c17576b6

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_star_eq`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Differentiation commutes with conjugation: the real Fréchet derivative of the pointwise conjugate `p ↦ star (f p)` is `conjCLE` (conjugation on `ℂ`) composed with `fderiv ℝ f u`; in physicists' notation, `d f̄ = conj(d f)`. Conjugation is `ℝ`-linear, so it slides through the real derivative unchanged, whereas it does *not* commute with the holomorphic Wirtinger derivative `∂_v`. The `star` conjugates the *output* `f p`, so this is not a derivative in a conjugate variable. This is the analytic core of the conjugation lemmas below (`dWirtingerDir_star_comp` and its dual): distributed over the Wirtinger split of `fderiv ℝ f u` (`realLinear_apply_eq_wirtinger`, §D), the outer `conjCLE` conjugates the two coefficients and swaps the holomorphic and anti-holomorphic parts.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Differentiation commutes with conjugation: the real Fréchet derivative of the pointwise conjugate `p ↦ star (f p)` is `conjCLE` (conjugation on `ℂ`) composed with `fderiv ℝ f u`; in physicists' notation, `d f̄ = conj(d f)`. Conjugation is `ℝ`-linear, so it slides through the real derivative unchanged, whereas it does *not* commute with the holomorphic Wirtinger derivative `∂_v`. The `star` conjugates the *output* `f p`, so this is not a derivative in a conjugate variable. This is the analytic core of the conjugation lemmas below (`dWirtingerDir_star_comp` and its dual): distributed over the Wirtinger split of `fderiv ℝ f u` (`realLinear_apply_eq_wirtinger`, §D), the outer `conjCLE` conjugates the two coefficients and swaps the holomorphic and anti-holomorphic parts. -/
lemma Physlib.Wirtinger.fderiv_star_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {u : E} (hf : DifferentiableAt ℝ f u) :
    fderiv ℝ (fun p : E => star (f p)) u =
      Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ f u) :=
  (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp u hf.hasFDerivAt).fderiv
