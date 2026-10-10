import AFTD.Prelude

/-!
# Physlib.Wirtinger.realLinear_apply_eq_wirtinger

Topic: classical_mechanics   Node: 0d9c8bfdec83

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.realLinear_apply_eq_wirtinger`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Split a real-linear map `ℂ → ℂ` into its Wirtinger components. Any real-linear `L : ℂ →L[ℝ] ℂ` splits into a holomorphic and an anti-holomorphic part with the Wirtinger coefficients `a = ½(L 1 - i * L i)`, `b = ½(L 1 + i * L i)` as weights: `L w = a * w + b * star w`. This is purely algebraic: `L` is an arbitrary real-linear map, no derivative involved. Its use is the Wirtinger chain rule (`dWirtingerDir_comp` below), where the weights of the outer differential `L = fderiv ℝ g (f u)` are the coefficients `∂g/∂f`, `∂g/∂f̄`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Split a real-linear map `ℂ → ℂ` into its Wirtinger components. Any real-linear `L : ℂ →L[ℝ] ℂ` splits into a holomorphic and an anti-holomorphic part with the Wirtinger coefficients `a = ½(L 1 - i * L i)`, `b = ½(L 1 + i * L i)` as weights: `L w = a * w + b * star w`. This is purely algebraic: `L` is an arbitrary real-linear map, no derivative involved. Its use is the Wirtinger chain rule (`dWirtingerDir_comp` below), where the weights of the outer differential `L = fderiv ℝ g (f u)` are the coefficients `∂g/∂f`, `∂g/∂f̄`. -/
lemma Physlib.Wirtinger.realLinear_apply_eq_wirtinger (L : ℂ →L[ℝ] ℂ) (w : ℂ) :
    L w =
      ((1 / 2 : ℂ) * (L 1 - Complex.I * L Complex.I)) * w
        + ((1 / 2 : ℂ) * (L 1 + Complex.I * L Complex.I)) * star w := by
  have hw : w = (w.re : ℝ) • (1 : ℂ) + (w.im : ℝ) • Complex.I := by
    apply Complex.ext <;> simp
  nth_rewrite 1 [hw, map_add, map_smul, map_smul]
  apply Complex.ext <;> simp <;> ring
