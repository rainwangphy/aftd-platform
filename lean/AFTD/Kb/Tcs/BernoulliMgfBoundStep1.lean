import AFTD.Prelude

/-!
# bernoulli_mgf_bound_step1

Topic: learning   Node: 8f65e56bc6c3

Provenance: helper lemma. TCSlib, `bernoulli_mgf_bound_step1`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Hoeffding.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

First derivative of the Hoeffding auxiliary function. Let $L, x \in \bbr$ and suppose $1 - L + L\,e^{-x} > 0$. Then the auxiliary function
\[
  \varphi(x) \;=\; -L x + \frac{x^2}{8} - \ln\!\bigl(1 - L + L\,e^{-x}\bigr)
\]
is differentiable at $x$ with derivative
\[
  \varphi'(x) \;=\; -L + \frac{x}{4} + \frac{L\,e^{-x}}{1 - L + L\,e^{-x}}.
\]
This is the $\varphi'$ computation used in the proof of $ bernoulli_mgf_bound$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators Real in
/-- Step lemma for `bernoulli_mgf_bound` (Step 5): at any `x` where `1 - L + L e^{-x} > 0`, the function `φ(x) = -L x + x²/8 - log(1 - L + L e^{-x})` has derivative `φ'(x) = -L + x/4 + L e^{-x} / (1 - L + L e^{-x})`. This is the `φ'` computation in the proof of [MRT18, Lemma D.1]. -/
lemma bernoulli_mgf_bound_step1 (L x : ℝ) (hpos : 0 < 1 - L + L * Real.exp (-x)) :
    HasDerivAt (fun x => -L * x + x ^ 2 / 8 - Real.log (1 - L + L * Real.exp (-x)))
      (-L + x / 4 + L * Real.exp (-x) / (1 - L + L * Real.exp (-x))) x := by
  have hne : 1 - L + L * Real.exp (-x) ≠ 0 := hpos.ne'
  have h_den : HasDerivAt (fun x => 1 - L + L * Real.exp (-x)) (L * (Real.exp (-x) * -1)) x :=
    ((hasDerivAt_neg' x).exp.const_mul L).const_add (1 - L)
  have h := (((hasDerivAt_id' x).const_mul (-L)).fun_add ((hasDerivAt_pow 2 x).div_const 8)).fun_sub
    (h_den.log hne)
  convert h using 1 <;> try rfl
  field_simp
  ring
