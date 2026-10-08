import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# BoolFourier.expectation_eq_expect

Topic: interactive   Node: 8689f06ab1c9

Provenance: helper lemma. TCSlib, `BoolFourier.expectation_eq_expect`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Agreement of two definitions of the uniform expectation. Let $n$ be a natural number and let $f : \{0,1\}^n \to \bbr$ be a Boolean function of
arity $n$. Then the two forms of the uniform expectation of $f$ coincide, namely
\[
  \frac{1}{2^n} \sum_{x \in \{0,1\}^n} f(x) \;=\; 2^{-n} \sum_{x \in \{0,1\}^n} f(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
lemma BoolFourier.expectation_eq_expect {n : ℕ} (f : BoolFun n) :
    expectation f = expect f := by
  unfold expectation BooleanAnalysis.expect BooleanAnalysis.uniformWeight
  rw [div_eq_mul_inv, ← inv_pow, mul_comm]

-- Bridge: BoolFourier.fourier_coeff ↔ BooleanAnalysis.fourierCoeff
