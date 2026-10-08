import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierInnerProduct
import AFTD.Kb.Tcs.BoolFourierExpectationEqExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct

/-!
# BoolFourier.fourier_coeff_eq

Topic: interactive   Node: 0fb7bb2b37df

Provenance: helper lemma. TCSlib, `BoolFourier.fourier_coeff_eq`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Agreement of two Fourier coefficient definitions. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function of arity $n$, and let $S \subseteq
[n]$. Then the two definitions of the Fourier–Walsh coefficient $\hat f(S)$ coincide:
both are equal to the $L^2$ inner product of $f$ with the Walsh character $\chi_S$,
\[
\hat f(S) \;=\; \langle f, \chi_S\rangle \;=\; 2^{-n}\sum_{x\in\{0,1\}^n}
f(x)\,\chi_S(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
lemma BoolFourier.fourier_coeff_eq {n : ℕ} (f : BoolFun n) (S : Finset (Fin n)) :
    fourier_coeff f S = fourierCoeff f S := by
  unfold fourier_coeff inner_product BooleanAnalysis.fourierCoeff BooleanAnalysis.innerProduct
  exact expectation_eq_expect _

-- f(x) = ∑_S f̂(S) χ_S(x)
