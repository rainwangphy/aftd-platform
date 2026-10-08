import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierConvolution
import AFTD.Kb.Tcs.BoolFourierExpectation
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BoolBLR.triple_expectation_eq_cube_fourier_aux_h_substitute

Topic: interactive   Node: 9bf43bec70cc

Provenance: helper lemma. TCSlib, `BoolBLR.triple_expectation_eq_cube_fourier_aux_h_substitute`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expectation of a function against its Fourier-expanded autocorrelation. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean function, and let $g$ denote its $\pm 1$
lift, so that $g(x) = (-1)^{f(x)}$. Suppose that the convolution of $g$ with itself
admits the Fourier expansion
\[
  (g * g)(x) \;=\; \sum_{S \subseteq [n]} \hat{g}(S)^2\,\chi_S(x)
  \qquad\text{for every } x \in \{0,1\}^n,
\]
where $\chi_S$ is the Walsh character of $S$ and $\hat{g}(S) = \langle g,
\chi_S\rangle$. Then
\[
  \E_x\!\left[g(x)\,(g * g)(x)\right]
  \;=\;
  \sum_{S \subseteq [n]} \hat{g}(S)^2\,\E_x\!\left[g(x)\,\chi_S(x)\right],
\]
the expectation being taken uniformly over $x \in \{0,1\}^n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.triple_expectation_eq_cube_fourier_aux_h_substitute {n : ℕ} (f : BoolFourier.hypercube n → Bool) (h_convolution : ∀ (x : BooleanAnalysis.BoolCube n),
  BoolFourier.convolution (lift_pm1 f) (lift_pm1 f) x =
    ∑ S, BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 * BoolFourier.char_S S x) :
    (BoolFourier.expectation fun x => lift_pm1 f x * BoolFourier.convolution (lift_pm1 f) (lift_pm1 f) x) =
  ∑ S,
    BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 *
      BoolFourier.expectation fun x => lift_pm1 f x * BoolFourier.char_S S x :=
  by
  simp +decide only [h_convolution, Finset.mul_sum _ _ _, expectation];
  rw [ Finset.sum_comm ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _] ;
