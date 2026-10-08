import AFTD.Prelude
import AFTD.Kb.Tcs.BernoulliMgfBoundStep1

/-!
# bernoulli_mgf_bound_step2

Topic: learning   Node: 00de5db74701

Provenance: helper lemma. TCSlib, `bernoulli_mgf_bound_step2`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Hedge/Hoeffding.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Second derivative of the Hoeffding auxiliary function. Let $L, x \in \bbr$ and suppose $1 - L + L\,e^{-x} > 0$. Then the function
\[
  \varphi'(x) \;=\; -L + \frac{x}{4} + \frac{L\,e^{-x}}{1 - L + L\,e^{-x}}
\]
(the derivative from $ bernoulli_mgf_bound_step1$) is differentiable at $x$ with
derivative
\[
  \varphi''(x) \;=\; \frac{1}{4} - \frac{L\,(1 - L)\,e^{-x}}{\bigl(1 - L + L\,e^{-x}\bigr)^2}.
\]
This is the $\varphi''$ computation used in the proof of $ bernoulli_mgf_bound$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators Real in
/-- Step lemma for `bernoulli_mgf_bound` (Step 5): at any `x` where `1 - L + L e^{-x} > 0`, the derivative `φ'` of `bernoulli_mgf_bound_step1` has itself derivative `φ''(x) = 1/4 - L (1 - L) e^{-x} / (1 - L + L e^{-x})²`. This is the `φ''` computation in the proof of [MRT18, Lemma D.1]. -/
lemma bernoulli_mgf_bound_step2 (L x : ℝ) (hpos : 0 < 1 - L + L * Real.exp (-x)) :
    HasDerivAt (fun x => -L + x / 4 + L * Real.exp (-x) / (1 - L + L * Real.exp (-x)))
      (1 / 4 - L * (1 - L) * Real.exp (-x) / (1 - L + L * Real.exp (-x)) ^ 2) x := by
  have hne : 1 - L + L * Real.exp (-x) ≠ 0 := hpos.ne'
  have h_num : HasDerivAt (fun x => L * Real.exp (-x)) (L * (Real.exp (-x) * -1)) x :=
    (hasDerivAt_neg' x).exp.const_mul L
  have h_den : HasDerivAt (fun x => 1 - L + L * Real.exp (-x)) (L * (Real.exp (-x) * -1)) x :=
    h_num.const_add (1 - L)
  have h := (((hasDerivAt_id' x).div_const 4).const_add (-L)).fun_add (h_num.fun_div h_den hne)
  convert h using 1 <;> try rfl
  field_simp
  ring
