import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# BoolFourier.fourier_coeff_convolution_aux_h_split

Topic: interactive   Node: d134e60b2c12

Provenance: helper lemma. TCSlib, `BoolFourier.fourier_coeff_convolution_aux_h_split`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multiplicative splitting of a Walsh character along XOR. Let $S \subseteq [n]$, let $f, g : \{0,1\}^n \to \bbr$ be Boolean functions, and suppose
the interchange-of-summation identity
\[
  \sum_{x} \Big(\sum_{y} f(y)\, g(x \oplus y)\Big)\,\chi_S(x)
  \;=\; \sum_{y} f(y) \sum_{x} g(x \oplus y)\,\chi_S(x)
\]
holds, where all sums range over $\{0,1\}^n$ and $\oplus$ is componentwise XOR. Then for
all $x, y \in \{0,1\}^n$,
\[
  \chi_S(x) \;=\; \chi_S(x \oplus y)\,\chi_S(y),
\]
where $\chi_S$ is the Walsh--Fourier character of $S$; that is, $\chi_S$ is a character
of the group $(\bbf_2)^n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
lemma BoolFourier.fourier_coeff_convolution_aux_h_split {n : Nat} (f g : BoolFun n) (S : Finset (Fin n))
  (_h_fubini : ∑ x, (∑ y, f y * g (xor_vec x y)) * char_S S x = ∑ y, f y * ∑ x, g (xor_vec x y) * char_S S x)
  (y x : hypercube n) : char_S S x = char_S S (xor_vec x y) * char_S S y := by
  simp [chiS, ← Finset.prod_mul_distrib]
  congr 1; ext i; simp [xor_vec, boolToSign, Bool.xor]
  cases x i <;> cases y i <;> simp
