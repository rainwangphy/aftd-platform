import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierConvolution
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierInnerProduct
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolutionAuxHChar
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolutionAuxHFubini

/-!
# BoolFourier.fourier_coeff_convolution

Topic: interactive   Node: 918d5e30b03a

Provenance: helper lemma. TCSlib, `BoolFourier.fourier_coeff_convolution`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convolution theorem on the Boolean cube. Let $n$ be a natural number, and let $f, g : \{0,1\}^n \to \bbr$ be Boolean functions.
Then for every subset $S \subseteq [n]$, the Fourier coefficient of the convolution $f *
g$ at $S$ equals the product of the Fourier coefficients of $f$ and $g$ at $S$:
\[
  \widehat{f * g}(S) = \hat f(S)\,\hat g(S).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
/-- States that the Fourier coefficient of a convolution is the product of coefficients. **Source:** [OD14, §1.5]. -/
lemma BoolFourier.fourier_coeff_convolution {n : ℕ} (f g : BoolFun n) (S : Finset (Fin n)) :
    fourier_coeff (convolution f g) S = fourier_coeff f S * fourier_coeff g S := by
  classical
  let h_char : ∀ y : hypercube n, ∑ x : hypercube n, g (xor_vec x y) * char_S S x = char_S S y * ∑ x : hypercube n, g x * char_S S x := (fourier_coeff_convolution_aux_h_char f g S (fourier_coeff_convolution_aux_h_fubini f g S))
  unfold convolution fourier_coeff inner_product expectation
  simp_all +decide [div_mul_eq_mul_div, ← Finset.sum_div, (fourier_coeff_convolution_aux_h_fubini f g S)]
  simp +decide only [← mul_assoc, ← Finset.sum_mul]; ring
