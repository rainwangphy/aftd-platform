import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierXorVec

/-!
# BoolFourier.fourier_coeff_convolution_aux_h_fubini

Topic: interactive   Node: 89bb38fb956c

Provenance: helper lemma. TCSlib, `BoolFourier.fourier_coeff_convolution_aux_h_fubini`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interchange of summation in the convolution coefficient. Let $n$ be a natural number, let $f, g : \{0,1\}^n \to \bbr$ be Boolean functions, and
let $S \subseteq [n]$ with associated Walsh character $\chi_S(x) = \prod_{i \in
S}(-1)^{x_i}$. Writing $x \oplus y$ for the componentwise XOR of $x, y \in \{0,1\}^n$,
the following identity holds:
\[
\sum_{x \in \{0,1\}^n} \Bigl(\sum_{y \in \{0,1\}^n} f(y)\,g(x \oplus y)\Bigr)\,\chi_S(x)
  \;=\;
  \sum_{y \in \{0,1\}^n} f(y) \sum_{x \in \{0,1\}^n} g(x \oplus y)\,\chi_S(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
lemma BoolFourier.fourier_coeff_convolution_aux_h_fubini {n : Nat} (f g : BoolFun n) (S : Finset (Fin n)) :
  ∑ x, (∑ y, f y * g (xor_vec x y)) * char_S S x = ∑ y, f y * ∑ x, g (xor_vec x y) * char_S S x := by
  simpa only [Finset.mul_sum _ _ _, mul_assoc, Finset.sum_mul] using Finset.sum_comm
