import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierConvolution
import AFTD.Kb.Tcs.BoolFourierFourierCoeff
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolution
import AFTD.Kb.Tcs.BoolFourierFourierExpansion
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# BoolBLR.triple_expectation_eq_cube_fourier_aux_h_convolution

Topic: interactive   Node: bbd8914720fa

Provenance: helper lemma. TCSlib, `BoolBLR.triple_expectation_eq_cube_fourier_aux_h_convolution`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fourier expansion of the self-convolution. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean-valued function, and let $g : \{0,1\}^n \to
\bbr$ be its $\pm 1$ lift, $g(x) = (-1)^{f(x)}$. Writing $g * g$ for the
self-convolution $(g * g)(x) = \E_{y}\bigl[g(y)\,g(x \oplus y)\bigr]$ with respect to
the uniform measure, and $\hat g(S) = \E[g\,\chi_S]$ for the Fourier coefficient of $g$
at $S$, one has for every $x \in \{0,1\}^n$
\[
  (g * g)(x) \;=\; \sum_{S \subseteq [n]} \hat g(S)^2\, \chi_S(x),
\]
where $\chi_S(x) = \prod_{i \in S} (-1)^{x_i}$ is the Walsh character of $S$. That is,
the self-convolution of $g$ has Fourier coefficients $\hat g(S)^2$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
lemma BoolBLR.triple_expectation_eq_cube_fourier_aux_h_convolution {n : ℕ} (f : BoolFourier.hypercube n → Bool) :
    ∀ (x : BooleanAnalysis.BoolCube n),
  BoolFourier.convolution (lift_pm1 f) (lift_pm1 f) x =
    ∑ S, BoolFourier.fourier_coeff (lift_pm1 f) S ^ 2 * BoolFourier.char_S S x :=
  by
  intro x;
  convert fourier_expansion ( BoolFourier.convolution ( lift_pm1 f ) ( lift_pm1 f ) ) x using 1;
  exact Finset.sum_congr rfl fun _ _ => by rw [ fourier_coeff_convolution ] ; ring;
