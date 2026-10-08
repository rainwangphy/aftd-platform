import AFTD.Prelude
import AFTD.Kb.Tcs.BoolFourierBoolFun
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolutionAuxHSplit

/-!
# BoolFourier.fourier_coeff_convolution_aux_h_char

Topic: interactive   Node: c477ad921eca

Provenance: helper lemma. TCSlib, `BoolFourier.fourier_coeff_convolution_aux_h_char`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolFourier.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Shift rule for character-weighted sums. Let $f, g : \{0,1\}^n \to \bbr$ be Boolean functions, let $S \subseteq [n]$, and write
$\chi_S(x) = \prod_{i \in S}(-1)^{x_i}$ for the associated Walsh character, where
$\oplus$ denotes componentwise XOR. Suppose the order of summation may be interchanged
in the double sum
\[
  \sum_{x}\Big(\sum_{y} f(y)\,g(x \oplus y)\Big)\chi_S(x)
  \;=\;
  \sum_{y} f(y)\sum_{x} g(x \oplus y)\,\chi_S(x).
\]
Then for every $y \in \{0,1\}^n$, translating the argument of $g$ by $y$ multiplies the
character-weighted sum by the factor $\chi_S(y)$:
\[
  \sum_{x} g(x \oplus y)\,\chi_S(x)
  \;=\;
  \chi_S(y)\sum_{x} g(x)\,\chi_S(x).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BooleanAnalysis in
lemma BoolFourier.fourier_coeff_convolution_aux_h_char {n : Nat} (f g : BoolFun n) (S : Finset (Fin n))
  (h_fubini : ∑ x, (∑ y, f y * g (xor_vec x y)) * char_S S x = ∑ y, f y * ∑ x, g (xor_vec x y) * char_S S x)
  (y : hypercube n) : ∑ x, g (xor_vec x y) * char_S S x = char_S S y * ∑ x, g x * char_S S x := by
  rw [Finset.mul_sum _ _ _]
  apply Finset.sum_bij (fun x _ => xor_vec x y)
  · exact fun _ _ => Finset.mem_univ _
  · unfold xor_vec; simp +decide
    exact fun a₁ a₂ h => funext fun i => by
      by_cases hi : y i <;> simpa [hi] using (congr_fun h i)
  · intro b _
    exact ⟨xor_vec b y, Finset.mem_univ _,
           funext fun i => by simp [xor_vec]⟩
  · exact fun x _ => by rw [(fourier_coeff_convolution_aux_h_split f g S h_fubini y) x]; ring
