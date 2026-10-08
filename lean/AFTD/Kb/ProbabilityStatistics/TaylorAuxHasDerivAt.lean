import AFTD.Prelude

/-!
# taylorAux_hasDerivAt

Topic: concentration   Node: 8616359ac4bc

Provenance: helper lemma. TCSlib, `taylorAux_hasDerivAt`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Derivative of a Taylor auxiliary function. Let $h \colon \bbr \to \bbr$ be the function $h(x) = x^2 + x + \log(1 - x)$. Then at
every point $u < 1$, the function $h$ is differentiable with derivative
\[
h'(u) = \frac{u(1 - 2u)}{1 - u}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- For `u < 1`, the auxiliary function `h(x) = x² + x + log(1 − x)` is differentiable at `u` with derivative `u(1 − 2u)/(1 − u)`. -/
lemma taylorAux_hasDerivAt (u : ℝ) (hu : u < 1) :
    HasDerivAt (fun x : ℝ => x ^ 2 + x + Real.log (1 - x))
      (u * (1 - 2 * u) / (1 - u)) u := by
  have hne : (1 - u : ℝ) ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u)
  have h2 : HasDerivAt (fun x : ℝ => x) 1 u := hasDerivAt_id u
  have h3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u :=
    (hasDerivAt_id u).const_sub 1
  have h4 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - u)) u :=
    h3.log hne
  have h5 := (h1.add h2).add h4
  -- Sum derivative: 2u + 1 + (-1/(1-u))
  -- Goal: 2u + 1 + (-1)/(1-u) = u(1-2u)/(1-u)
  convert h5 using 1 <;> try rfl
  field_simp
  ring
