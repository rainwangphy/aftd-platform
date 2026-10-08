import AFTD.Prelude

/-!
# taylorAux_zero

Topic: concentration   Node: c35c0e0f0d37

Provenance: helper lemma. TCSlib, `taylorAux_zero`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An auxiliary expression vanishes at zero. The real-valued expression $x^2 + x + \log(1 - x)$ takes the value $0$ at $x = 0$; that
is, $0^2 + 0 + \log(1 - 0) = 0$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- The auxiliary function `h(x) = x² + x + log(1 − x)` vanishes at `x = 0`. -/
lemma taylorAux_zero : ((0 : ℝ) ^ 2 + (0 : ℝ) + Real.log (1 - (0 : ℝ))) = 0 := by
  simp
